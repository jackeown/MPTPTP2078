%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:31 EST 2020

% Result     : Theorem 55.30s
% Output     : CNFRefutation 55.30s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 466 expanded)
%              Number of clauses        :   93 ( 171 expanded)
%              Number of leaves         :   25 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  634 (1722 expanded)
%              Number of equality atoms :  182 ( 650 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f66,f67])).

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

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
        & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f81,f67])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 != k10_relat_1(sK9,sK8) )
      & ( r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 = k10_relat_1(sK9,sK8) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 != k10_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 = k10_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f48,f49])).

fof(f83,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f70])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f72,f67])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f38,f41,f40,f39])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f84,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_199563,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0)
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_199565,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_199563])).

cnf(c_348,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_195654,plain,
    ( sK6(sK9,sK3(k2_relat_1(sK9),sK8)) = sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_351,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_172692,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | X1 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | X0 != sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_195653,plain,
    ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | X0 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | sK6(sK9,sK3(k2_relat_1(sK9),sK8)) != sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_172692])).

cnf(c_195656,plain,
    ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k1_xboole_0)
    | sK6(sK9,sK3(k2_relat_1(sK9),sK8)) != sK6(sK9,sK3(k2_relat_1(sK9),sK8))
    | k1_xboole_0 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_195653])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_172701,plain,
    ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_172703,plain,
    ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)))
    | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_172701])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_156495,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,X1))
    | ~ r2_hidden(k4_tarski(X0,sK3(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),X1)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_158463,plain,
    ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,X0))
    | ~ r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),X0)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_156495])).

cnf(c_166169,plain,
    ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
    | ~ r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_158463])).

cnf(c_352,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_21153,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_352,c_348])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_349,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_31,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1841,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 != k10_relat_1(sK9,sK8)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_349,c_31])).

cnf(c_5549,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(sK9)
    | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
    inference(resolution,[status(thm)],[c_29,c_1841])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_68,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1843,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_349,c_348])).

cnf(c_1935,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1843,c_31])).

cnf(c_1949,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 != k1_xboole_0
    | k10_relat_1(sK9,sK8) = X0 ),
    inference(resolution,[status(thm)],[c_1935,c_349])).

cnf(c_2053,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 = k10_relat_1(sK9,sK8)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1949,c_1843])).

cnf(c_2495,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | X0 = X1
    | X1 != k10_relat_1(sK9,sK8)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2053,c_349])).

cnf(c_5545,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(sK9)
    | X0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_2495])).

cnf(c_5547,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ v1_relat_1(sK9)
    | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5545])).

cnf(c_6607,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5549,c_32,c_67,c_68,c_5547])).

cnf(c_6625,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6607,c_1843])).

cnf(c_21706,plain,
    ( r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0)
    | r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_21153,c_6625])).

cnf(c_21708,plain,
    ( r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21706])).

cnf(c_985,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_999,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_996,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1348,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_996])).

cnf(c_2348,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_1348])).

cnf(c_998,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1068,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_998,c_20])).

cnf(c_16929,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2348,c_1068])).

cnf(c_20442,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_985,c_16929])).

cnf(c_1485,plain,
    ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
    | r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1759,plain,
    ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),sK8)
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1758,plain,
    ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9))
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2283,plain,
    ( ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2289,plain,
    ( ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_2639,plain,
    ( sK2(k10_relat_1(sK9,sK8),k1_xboole_0) = sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_1690,plain,
    ( X0 != X1
    | k10_relat_1(sK9,sK8) != X1
    | k10_relat_1(sK9,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_2806,plain,
    ( X0 != k10_relat_1(sK9,sK8)
    | k10_relat_1(sK9,sK8) = X0
    | k10_relat_1(sK9,sK8) != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2808,plain,
    ( k10_relat_1(sK9,sK8) != k10_relat_1(sK9,sK8)
    | k10_relat_1(sK9,sK8) = k1_xboole_0
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_2807,plain,
    ( k10_relat_1(sK9,sK8) = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_2123,plain,
    ( ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),X0)
    | r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),X0)))
    | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3585,plain,
    ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9))
    | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_8933,plain,
    ( k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1517,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
    | X0 != sK2(k10_relat_1(sK9,sK8),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_2638,plain,
    ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0)
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
    | X0 != k1_xboole_0
    | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_8985,plain,
    ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0))
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0) != k1_xboole_0
    | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_8987,plain,
    ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0))
    | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8985])).

cnf(c_16592,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_20454,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20442,c_32,c_1485,c_1759,c_1758,c_1935,c_2289,c_2639,c_2808,c_2807,c_3585,c_8933,c_8987,c_16592])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2075,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_5585,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | r2_hidden(X0,k10_relat_1(sK9,sK8))
    | ~ r2_hidden(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_351,c_1935])).

cnf(c_6046,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | r2_hidden(X0,k10_relat_1(sK9,sK8))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5585,c_348])).

cnf(c_1354,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1348])).

cnf(c_9722,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6046,c_1354])).

cnf(c_12733,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2075,c_9722])).

cnf(c_12735,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12733])).

cnf(c_2057,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(resolution,[status(thm)],[c_1949,c_1841])).

cnf(c_1489,plain,
    ( k10_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_1490,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2480,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2057,c_67,c_68,c_1490])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1576,plain,
    ( r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1417,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
    | r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1295,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_30,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_199565,c_195654,c_195656,c_172703,c_166169,c_21708,c_20454,c_12735,c_5547,c_2480,c_1576,c_1417,c_1295,c_68,c_67,c_30,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:56:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.30/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.30/7.50  
% 55.30/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.30/7.50  
% 55.30/7.50  ------  iProver source info
% 55.30/7.50  
% 55.30/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.30/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.30/7.50  git: non_committed_changes: false
% 55.30/7.50  git: last_make_outside_of_git: false
% 55.30/7.50  
% 55.30/7.50  ------ 
% 55.30/7.50  ------ Parsing...
% 55.30/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.30/7.50  
% 55.30/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 55.30/7.50  
% 55.30/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.30/7.50  
% 55.30/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.30/7.50  ------ Proving...
% 55.30/7.50  ------ Problem Properties 
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  clauses                                 33
% 55.30/7.50  conjectures                             3
% 55.30/7.50  EPR                                     1
% 55.30/7.50  Horn                                    22
% 55.30/7.50  unary                                   5
% 55.30/7.50  binary                                  11
% 55.30/7.50  lits                                    82
% 55.30/7.50  lits eq                                 19
% 55.30/7.50  fd_pure                                 0
% 55.30/7.50  fd_pseudo                               0
% 55.30/7.50  fd_cond                                 1
% 55.30/7.50  fd_pseudo_cond                          10
% 55.30/7.50  AC symbols                              0
% 55.30/7.50  
% 55.30/7.50  ------ Input Options Time Limit: Unbounded
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  ------ 
% 55.30/7.50  Current options:
% 55.30/7.50  ------ 
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  ------ Proving...
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  % SZS status Theorem for theBenchmark.p
% 55.30/7.50  
% 55.30/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.30/7.50  
% 55.30/7.50  fof(f4,axiom,(
% 55.30/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f14,plain,(
% 55.30/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.30/7.50    inference(rectify,[],[f4])).
% 55.30/7.50  
% 55.30/7.50  fof(f16,plain,(
% 55.30/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.30/7.50    inference(ennf_transformation,[],[f14])).
% 55.30/7.50  
% 55.30/7.50  fof(f33,plain,(
% 55.30/7.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f34,plain,(
% 55.30/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f33])).
% 55.30/7.50  
% 55.30/7.50  fof(f66,plain,(
% 55.30/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 55.30/7.50    inference(cnf_transformation,[],[f34])).
% 55.30/7.50  
% 55.30/7.50  fof(f5,axiom,(
% 55.30/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f67,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.30/7.50    inference(cnf_transformation,[],[f5])).
% 55.30/7.50  
% 55.30/7.50  fof(f91,plain,(
% 55.30/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.30/7.50    inference(definition_unfolding,[],[f66,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f1,axiom,(
% 55.30/7.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f20,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(nnf_transformation,[],[f1])).
% 55.30/7.50  
% 55.30/7.50  fof(f21,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(flattening,[],[f20])).
% 55.30/7.50  
% 55.30/7.50  fof(f22,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(rectify,[],[f21])).
% 55.30/7.50  
% 55.30/7.50  fof(f23,plain,(
% 55.30/7.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f24,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 55.30/7.50  
% 55.30/7.50  fof(f53,plain,(
% 55.30/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 55.30/7.50    inference(cnf_transformation,[],[f24])).
% 55.30/7.50  
% 55.30/7.50  fof(f88,plain,(
% 55.30/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 55.30/7.50    inference(definition_unfolding,[],[f53,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f95,plain,(
% 55.30/7.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 55.30/7.50    inference(equality_resolution,[],[f88])).
% 55.30/7.50  
% 55.30/7.50  fof(f10,axiom,(
% 55.30/7.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f17,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 55.30/7.50    inference(ennf_transformation,[],[f10])).
% 55.30/7.50  
% 55.30/7.50  fof(f43,plain,(
% 55.30/7.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 55.30/7.50    inference(nnf_transformation,[],[f17])).
% 55.30/7.50  
% 55.30/7.50  fof(f44,plain,(
% 55.30/7.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 55.30/7.50    inference(rectify,[],[f43])).
% 55.30/7.50  
% 55.30/7.50  fof(f45,plain,(
% 55.30/7.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f46,plain,(
% 55.30/7.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 55.30/7.50  
% 55.30/7.50  fof(f80,plain,(
% 55.30/7.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f46])).
% 55.30/7.50  
% 55.30/7.50  fof(f11,axiom,(
% 55.30/7.50    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f18,plain,(
% 55.30/7.50    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 55.30/7.50    inference(ennf_transformation,[],[f11])).
% 55.30/7.50  
% 55.30/7.50  fof(f81,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f18])).
% 55.30/7.50  
% 55.30/7.50  fof(f94,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 55.30/7.50    inference(definition_unfolding,[],[f81,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f12,conjecture,(
% 55.30/7.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f13,negated_conjecture,(
% 55.30/7.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 55.30/7.50    inference(negated_conjecture,[],[f12])).
% 55.30/7.50  
% 55.30/7.50  fof(f19,plain,(
% 55.30/7.50    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 55.30/7.50    inference(ennf_transformation,[],[f13])).
% 55.30/7.50  
% 55.30/7.50  fof(f47,plain,(
% 55.30/7.50    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 55.30/7.50    inference(nnf_transformation,[],[f19])).
% 55.30/7.50  
% 55.30/7.50  fof(f48,plain,(
% 55.30/7.50    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 55.30/7.50    inference(flattening,[],[f47])).
% 55.30/7.50  
% 55.30/7.50  fof(f49,plain,(
% 55.30/7.50    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f50,plain,(
% 55.30/7.50    (~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f48,f49])).
% 55.30/7.50  
% 55.30/7.50  fof(f83,plain,(
% 55.30/7.50    r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)),
% 55.30/7.50    inference(cnf_transformation,[],[f50])).
% 55.30/7.50  
% 55.30/7.50  fof(f82,plain,(
% 55.30/7.50    v1_relat_1(sK9)),
% 55.30/7.50    inference(cnf_transformation,[],[f50])).
% 55.30/7.50  
% 55.30/7.50  fof(f6,axiom,(
% 55.30/7.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f35,plain,(
% 55.30/7.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 55.30/7.50    inference(nnf_transformation,[],[f6])).
% 55.30/7.50  
% 55.30/7.50  fof(f36,plain,(
% 55.30/7.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 55.30/7.50    inference(flattening,[],[f35])).
% 55.30/7.50  
% 55.30/7.50  fof(f68,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 55.30/7.50    inference(cnf_transformation,[],[f36])).
% 55.30/7.50  
% 55.30/7.50  fof(f69,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 55.30/7.50    inference(cnf_transformation,[],[f36])).
% 55.30/7.50  
% 55.30/7.50  fof(f102,plain,(
% 55.30/7.50    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 55.30/7.50    inference(equality_resolution,[],[f69])).
% 55.30/7.50  
% 55.30/7.50  fof(f3,axiom,(
% 55.30/7.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f15,plain,(
% 55.30/7.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 55.30/7.50    inference(ennf_transformation,[],[f3])).
% 55.30/7.50  
% 55.30/7.50  fof(f30,plain,(
% 55.30/7.50    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 55.30/7.50    inference(nnf_transformation,[],[f15])).
% 55.30/7.50  
% 55.30/7.50  fof(f31,plain,(
% 55.30/7.50    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f32,plain,(
% 55.30/7.50    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 55.30/7.50  
% 55.30/7.50  fof(f63,plain,(
% 55.30/7.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f32])).
% 55.30/7.50  
% 55.30/7.50  fof(f70,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 55.30/7.50    inference(cnf_transformation,[],[f36])).
% 55.30/7.50  
% 55.30/7.50  fof(f101,plain,(
% 55.30/7.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.30/7.50    inference(equality_resolution,[],[f70])).
% 55.30/7.50  
% 55.30/7.50  fof(f7,axiom,(
% 55.30/7.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f71,plain,(
% 55.30/7.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 55.30/7.50    inference(cnf_transformation,[],[f7])).
% 55.30/7.50  
% 55.30/7.50  fof(f8,axiom,(
% 55.30/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f72,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.30/7.50    inference(cnf_transformation,[],[f8])).
% 55.30/7.50  
% 55.30/7.50  fof(f93,plain,(
% 55.30/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.30/7.50    inference(definition_unfolding,[],[f72,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f79,plain,(
% 55.30/7.50    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f46])).
% 55.30/7.50  
% 55.30/7.50  fof(f77,plain,(
% 55.30/7.50    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f46])).
% 55.30/7.50  
% 55.30/7.50  fof(f2,axiom,(
% 55.30/7.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f25,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(nnf_transformation,[],[f2])).
% 55.30/7.50  
% 55.30/7.50  fof(f26,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(flattening,[],[f25])).
% 55.30/7.50  
% 55.30/7.50  fof(f27,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(rectify,[],[f26])).
% 55.30/7.50  
% 55.30/7.50  fof(f28,plain,(
% 55.30/7.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f29,plain,(
% 55.30/7.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 55.30/7.50  
% 55.30/7.50  fof(f57,plain,(
% 55.30/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 55.30/7.50    inference(cnf_transformation,[],[f29])).
% 55.30/7.50  
% 55.30/7.50  fof(f100,plain,(
% 55.30/7.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 55.30/7.50    inference(equality_resolution,[],[f57])).
% 55.30/7.50  
% 55.30/7.50  fof(f65,plain,(
% 55.30/7.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 55.30/7.50    inference(cnf_transformation,[],[f34])).
% 55.30/7.50  
% 55.30/7.50  fof(f92,plain,(
% 55.30/7.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 55.30/7.50    inference(definition_unfolding,[],[f65,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f9,axiom,(
% 55.30/7.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 55.30/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.30/7.50  
% 55.30/7.50  fof(f37,plain,(
% 55.30/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 55.30/7.50    inference(nnf_transformation,[],[f9])).
% 55.30/7.50  
% 55.30/7.50  fof(f38,plain,(
% 55.30/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.30/7.50    inference(rectify,[],[f37])).
% 55.30/7.50  
% 55.30/7.50  fof(f41,plain,(
% 55.30/7.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f40,plain,(
% 55.30/7.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f39,plain,(
% 55.30/7.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 55.30/7.50    introduced(choice_axiom,[])).
% 55.30/7.50  
% 55.30/7.50  fof(f42,plain,(
% 55.30/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.30/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f38,f41,f40,f39])).
% 55.30/7.50  
% 55.30/7.50  fof(f73,plain,(
% 55.30/7.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 55.30/7.50    inference(cnf_transformation,[],[f42])).
% 55.30/7.50  
% 55.30/7.50  fof(f104,plain,(
% 55.30/7.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 55.30/7.50    inference(equality_resolution,[],[f73])).
% 55.30/7.50  
% 55.30/7.50  fof(f51,plain,(
% 55.30/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 55.30/7.50    inference(cnf_transformation,[],[f24])).
% 55.30/7.50  
% 55.30/7.50  fof(f90,plain,(
% 55.30/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 55.30/7.50    inference(definition_unfolding,[],[f51,f67])).
% 55.30/7.50  
% 55.30/7.50  fof(f97,plain,(
% 55.30/7.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.30/7.50    inference(equality_resolution,[],[f90])).
% 55.30/7.50  
% 55.30/7.50  fof(f84,plain,(
% 55.30/7.50    ~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)),
% 55.30/7.50    inference(cnf_transformation,[],[f50])).
% 55.30/7.50  
% 55.30/7.50  cnf(c_14,plain,
% 55.30/7.50      ( ~ r1_xboole_0(X0,X1)
% 55.30/7.50      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 55.30/7.50      inference(cnf_transformation,[],[f91]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_199563,plain,
% 55.30/7.50      ( ~ r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0)
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_14]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_199565,plain,
% 55.30/7.50      ( ~ r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_199563]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_348,plain,( X0 = X0 ),theory(equality) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_195654,plain,
% 55.30/7.50      ( sK6(sK9,sK3(k2_relat_1(sK9),sK8)) = sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_351,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.30/7.50      theory(equality) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_172692,plain,
% 55.30/7.50      ( r2_hidden(X0,X1)
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | X1 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | X0 != sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_351]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_195653,plain,
% 55.30/7.50      ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),X0)
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | X0 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | sK6(sK9,sK3(k2_relat_1(sK9),sK8)) != sK6(sK9,sK3(k2_relat_1(sK9),sK8)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_172692]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_195656,plain,
% 55.30/7.50      ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k1_xboole_0)
% 55.30/7.50      | sK6(sK9,sK3(k2_relat_1(sK9),sK8)) != sK6(sK9,sK3(k2_relat_1(sK9),sK8))
% 55.30/7.50      | k1_xboole_0 != k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_195653]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_3,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,X1)
% 55.30/7.50      | ~ r2_hidden(X0,X2)
% 55.30/7.50      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 55.30/7.50      inference(cnf_transformation,[],[f95]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_172701,plain,
% 55.30/7.50      ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),X0)
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_3]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_172703,plain,
% 55.30/7.50      ( ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k4_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)))
% 55.30/7.50      | ~ r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_172701]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_25,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,X1)
% 55.30/7.50      | r2_hidden(X2,k10_relat_1(X3,X1))
% 55.30/7.50      | ~ r2_hidden(X0,k2_relat_1(X3))
% 55.30/7.50      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 55.30/7.50      | ~ v1_relat_1(X3) ),
% 55.30/7.50      inference(cnf_transformation,[],[f80]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_156495,plain,
% 55.30/7.50      ( r2_hidden(X0,k10_relat_1(sK9,X1))
% 55.30/7.50      | ~ r2_hidden(k4_tarski(X0,sK3(k2_relat_1(sK9),sK8)),sK9)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),X1)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 55.30/7.50      | ~ v1_relat_1(sK9) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_25]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_158463,plain,
% 55.30/7.50      ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,X0))
% 55.30/7.50      | ~ r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),X0)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 55.30/7.50      | ~ v1_relat_1(sK9) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_156495]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_166169,plain,
% 55.30/7.50      ( r2_hidden(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))))
% 55.30/7.50      | ~ r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 55.30/7.50      | ~ v1_relat_1(sK9) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_158463]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_352,plain,
% 55.30/7.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.30/7.50      theory(equality) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_21153,plain,
% 55.30/7.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_352,c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_29,plain,
% 55.30/7.50      ( ~ v1_relat_1(X0)
% 55.30/7.50      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 55.30/7.50      inference(cnf_transformation,[],[f94]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_349,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_31,negated_conjecture,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(cnf_transformation,[],[f83]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1841,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | X0 != k10_relat_1(sK9,sK8)
% 55.30/7.50      | k1_xboole_0 = X0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_349,c_31]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_5549,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ v1_relat_1(sK9)
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_29,c_1841]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_32,negated_conjecture,
% 55.30/7.50      ( v1_relat_1(sK9) ),
% 55.30/7.50      inference(cnf_transformation,[],[f82]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_18,plain,
% 55.30/7.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 55.30/7.50      | k1_xboole_0 = X1
% 55.30/7.50      | k1_xboole_0 = X0 ),
% 55.30/7.50      inference(cnf_transformation,[],[f68]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_67,plain,
% 55.30/7.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 55.30/7.50      | k1_xboole_0 = k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_18]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_17,plain,
% 55.30/7.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.30/7.50      inference(cnf_transformation,[],[f102]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_68,plain,
% 55.30/7.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_17]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1843,plain,
% 55.30/7.50      ( X0 != X1 | X1 = X0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_349,c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1935,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_1843,c_31]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1949,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | X0 != k1_xboole_0
% 55.30/7.50      | k10_relat_1(sK9,sK8) = X0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_1935,c_349]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2053,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | X0 = k10_relat_1(sK9,sK8)
% 55.30/7.50      | X0 != k1_xboole_0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_1949,c_1843]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2495,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | X0 = X1
% 55.30/7.50      | X1 != k10_relat_1(sK9,sK8)
% 55.30/7.50      | X0 != k1_xboole_0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_2053,c_349]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_5545,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ v1_relat_1(sK9)
% 55.30/7.50      | X0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | X0 != k1_xboole_0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_29,c_2495]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_5547,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ v1_relat_1(sK9)
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_5545]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_6607,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
% 55.30/7.50      inference(global_propositional_subsumption,
% 55.30/7.50                [status(thm)],
% 55.30/7.50                [c_5549,c_32,c_67,c_68,c_5547]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_6625,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) = k1_xboole_0 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_6607,c_1843]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_21706,plain,
% 55.30/7.50      ( r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),X0)
% 55.30/7.50      | r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ r1_xboole_0(k1_xboole_0,X0) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_21153,c_6625]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_21708,plain,
% 55.30/7.50      ( r1_xboole_0(k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))),k1_xboole_0)
% 55.30/7.50      | r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_21706]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_985,plain,
% 55.30/7.50      ( k1_xboole_0 = k10_relat_1(sK9,sK8)
% 55.30/7.50      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 55.30/7.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_13,plain,
% 55.30/7.50      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 55.30/7.50      inference(cnf_transformation,[],[f63]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_999,plain,
% 55.30/7.50      ( X0 = X1
% 55.30/7.50      | r2_hidden(sK2(X1,X0),X0) = iProver_top
% 55.30/7.50      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 55.30/7.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_16,plain,
% 55.30/7.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 55.30/7.50      inference(cnf_transformation,[],[f101]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_19,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 55.30/7.50      inference(cnf_transformation,[],[f71]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_996,plain,
% 55.30/7.50      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 55.30/7.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1348,plain,
% 55.30/7.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.30/7.50      inference(superposition,[status(thm)],[c_16,c_996]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2348,plain,
% 55.30/7.50      ( k1_xboole_0 = X0
% 55.30/7.50      | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
% 55.30/7.50      inference(superposition,[status(thm)],[c_999,c_1348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_998,plain,
% 55.30/7.50      ( r1_xboole_0(X0,X1) != iProver_top
% 55.30/7.50      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 55.30/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_20,plain,
% 55.30/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 55.30/7.50      inference(cnf_transformation,[],[f93]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1068,plain,
% 55.30/7.50      ( r1_xboole_0(X0,X1) != iProver_top
% 55.30/7.50      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 55.30/7.50      inference(light_normalisation,[status(thm)],[c_998,c_20]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_16929,plain,
% 55.30/7.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 55.30/7.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.30/7.50      inference(superposition,[status(thm)],[c_2348,c_1068]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_20442,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 55.30/7.50      | k1_setfam_1(k2_tarski(k2_relat_1(sK9),sK8)) = k1_xboole_0 ),
% 55.30/7.50      inference(superposition,[status(thm)],[c_985,c_16929]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1485,plain,
% 55.30/7.50      ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
% 55.30/7.50      | r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_13]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_26,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 55.30/7.50      | r2_hidden(sK7(X0,X2,X1),X2)
% 55.30/7.50      | ~ v1_relat_1(X1) ),
% 55.30/7.50      inference(cnf_transformation,[],[f79]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1759,plain,
% 55.30/7.50      ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),sK8)
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
% 55.30/7.50      | ~ v1_relat_1(sK9) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_26]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_28,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 55.30/7.50      | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
% 55.30/7.50      | ~ v1_relat_1(X1) ),
% 55.30/7.50      inference(cnf_transformation,[],[f77]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1758,plain,
% 55.30/7.50      ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9))
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k10_relat_1(sK9,sK8))
% 55.30/7.50      | ~ v1_relat_1(sK9) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_28]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2283,plain,
% 55.30/7.50      ( ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_19]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2289,plain,
% 55.30/7.50      ( ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_2283]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2639,plain,
% 55.30/7.50      ( sK2(k10_relat_1(sK9,sK8),k1_xboole_0) = sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1690,plain,
% 55.30/7.50      ( X0 != X1
% 55.30/7.50      | k10_relat_1(sK9,sK8) != X1
% 55.30/7.50      | k10_relat_1(sK9,sK8) = X0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_349]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2806,plain,
% 55.30/7.50      ( X0 != k10_relat_1(sK9,sK8)
% 55.30/7.50      | k10_relat_1(sK9,sK8) = X0
% 55.30/7.50      | k10_relat_1(sK9,sK8) != k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_1690]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2808,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) != k10_relat_1(sK9,sK8)
% 55.30/7.50      | k10_relat_1(sK9,sK8) = k1_xboole_0
% 55.30/7.50      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_2806]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2807,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2123,plain,
% 55.30/7.50      ( ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),X0)
% 55.30/7.50      | r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),X0)))
% 55.30/7.50      | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_3]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_3585,plain,
% 55.30/7.50      ( r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k2_relat_1(sK9))
% 55.30/7.50      | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_2123]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_8933,plain,
% 55.30/7.50      ( k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_16]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1517,plain,
% 55.30/7.50      ( r2_hidden(X0,X1)
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
% 55.30/7.50      | X0 != sK2(k10_relat_1(sK9,sK8),k1_xboole_0)
% 55.30/7.50      | X1 != k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_351]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2638,plain,
% 55.30/7.50      ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0)
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
% 55.30/7.50      | X0 != k1_xboole_0
% 55.30/7.50      | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_1517]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_8985,plain,
% 55.30/7.50      ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0))
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
% 55.30/7.50      | k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),X0) != k1_xboole_0
% 55.30/7.50      | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_2638]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_8987,plain,
% 55.30/7.50      ( r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0))
% 55.30/7.50      | ~ r2_hidden(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0)
% 55.30/7.50      | k2_zfmisc_1(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 55.30/7.50      | sK2(k10_relat_1(sK9,sK8),k1_xboole_0) != sK2(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_8985]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_16592,plain,
% 55.30/7.50      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | ~ r2_hidden(sK7(sK2(k10_relat_1(sK9,sK8),k1_xboole_0),sK8,sK9),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_14]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_20454,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 55.30/7.50      inference(global_propositional_subsumption,
% 55.30/7.50                [status(thm)],
% 55.30/7.50                [c_20442,c_32,c_1485,c_1759,c_1758,c_1935,c_2289,c_2639,
% 55.30/7.50                 c_2808,c_2807,c_3585,c_8933,c_8987,c_16592]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_11,plain,
% 55.30/7.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 55.30/7.50      inference(cnf_transformation,[],[f100]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_15,plain,
% 55.30/7.50      ( r1_xboole_0(X0,X1)
% 55.30/7.50      | r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 55.30/7.50      inference(cnf_transformation,[],[f92]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2075,plain,
% 55.30/7.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_11,c_15]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_5585,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | r2_hidden(X0,k10_relat_1(sK9,sK8))
% 55.30/7.50      | ~ r2_hidden(X1,k1_xboole_0)
% 55.30/7.50      | X0 != X1 ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_351,c_1935]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_6046,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | r2_hidden(X0,k10_relat_1(sK9,sK8))
% 55.30/7.50      | ~ r2_hidden(X0,k1_xboole_0) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_5585,c_348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1354,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 55.30/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_1348]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_9722,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 55.30/7.50      inference(global_propositional_subsumption,
% 55.30/7.50                [status(thm)],
% 55.30/7.50                [c_6046,c_1354]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_12733,plain,
% 55.30/7.50      ( r1_xboole_0(k1_xboole_0,X0) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_2075,c_9722]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_12735,plain,
% 55.30/7.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_12733]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2057,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k10_relat_1(sK9,sK8) != k1_xboole_0
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(resolution,[status(thm)],[c_1949,c_1841]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1489,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) != X0
% 55.30/7.50      | k1_xboole_0 != X0
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_349]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1490,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8)
% 55.30/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_1489]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_2480,plain,
% 55.30/7.50      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 55.30/7.50      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(global_propositional_subsumption,
% 55.30/7.50                [status(thm)],
% 55.30/7.50                [c_2057,c_67,c_68,c_1490]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_24,plain,
% 55.30/7.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 55.30/7.50      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 55.30/7.50      inference(cnf_transformation,[],[f104]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1576,plain,
% 55.30/7.50      ( r2_hidden(k4_tarski(sK6(sK9,sK3(k2_relat_1(sK9),sK8)),sK3(k2_relat_1(sK9),sK8)),sK9)
% 55.30/7.50      | ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_24]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_5,plain,
% 55.30/7.50      ( r2_hidden(X0,X1)
% 55.30/7.50      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 55.30/7.50      inference(cnf_transformation,[],[f97]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1417,plain,
% 55.30/7.50      ( ~ r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8)))
% 55.30/7.50      | r2_hidden(sK3(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_5]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_1295,plain,
% 55.30/7.50      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | r2_hidden(sK3(k2_relat_1(sK9),sK8),k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),sK8))) ),
% 55.30/7.50      inference(instantiation,[status(thm)],[c_15]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(c_30,negated_conjecture,
% 55.30/7.50      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 55.30/7.50      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 55.30/7.50      inference(cnf_transformation,[],[f84]) ).
% 55.30/7.50  
% 55.30/7.50  cnf(contradiction,plain,
% 55.30/7.50      ( $false ),
% 55.30/7.50      inference(minisat,
% 55.30/7.50                [status(thm)],
% 55.30/7.50                [c_199565,c_195654,c_195656,c_172703,c_166169,c_21708,
% 55.30/7.50                 c_20454,c_12735,c_5547,c_2480,c_1576,c_1417,c_1295,c_68,
% 55.30/7.50                 c_67,c_30,c_32]) ).
% 55.30/7.50  
% 55.30/7.50  
% 55.30/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.30/7.50  
% 55.30/7.50  ------                               Statistics
% 55.30/7.50  
% 55.30/7.50  ------ Selected
% 55.30/7.50  
% 55.30/7.50  total_time:                             6.943
% 55.30/7.50  
%------------------------------------------------------------------------------
