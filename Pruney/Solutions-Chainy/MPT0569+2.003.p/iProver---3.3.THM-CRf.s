%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:27 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 296 expanded)
%              Number of clauses        :   78 (  98 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  441 (1052 expanded)
%              Number of equality atoms :  125 ( 300 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 != k10_relat_1(sK4,sK3) )
      & ( r1_xboole_0(k2_relat_1(sK4),sK3)
        | k1_xboole_0 = k10_relat_1(sK4,sK3) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 != k10_relat_1(sK4,sK3) )
    & ( r1_xboole_0(k2_relat_1(sK4),sK3)
      | k1_xboole_0 = k10_relat_1(sK4,sK3) )
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f44])).

fof(f71,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f73,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14420,plain,
    ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),X0)
    | ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k10_relat_1(sK4,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20249,plain,
    ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_14420])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_410,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_411,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_411,c_359])).

cnf(c_1757,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_7359,plain,
    ( r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_475,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_7283,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_770,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1780,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | X0 != sK0(k2_relat_1(sK4),sK3)
    | X1 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2622,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | X0 != k2_relat_1(sK4)
    | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_4785,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4)))
    | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4)
    | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2622])).

cnf(c_25,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1349,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1360,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1552,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1349,c_1360])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_498,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_499,plain,
    ( k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),X0))) = k10_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_2257,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k10_relat_1(sK4,k1_xboole_0) = k10_relat_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1552,c_499])).

cnf(c_24,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
    | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1350,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4223,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2257,c_1350])).

cnf(c_29,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_70,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_73,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_76,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_766,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1529,plain,
    ( k10_relat_1(sK4,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1530,plain,
    ( k10_relat_1(sK4,sK3) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK4,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1357,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_451,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(sK2(X0,X1,sK4),X1) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_1342,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_1353,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1351,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1702,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1351])).

cnf(c_2249,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1702])).

cnf(c_3670,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_2249])).

cnf(c_1354,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1352,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1931,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1352])).

cnf(c_2381,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1931])).

cnf(c_3692,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3670,c_2381])).

cnf(c_4226,plain,
    ( r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4223,c_29,c_70,c_73,c_76,c_1530,c_3692])).

cnf(c_765,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2218,plain,
    ( sK0(k2_relat_1(sK4),sK3) = sK0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1359,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1473,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | r1_xboole_0(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1359])).

cnf(c_2172,plain,
    ( k10_relat_1(sK4,sK3) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1359])).

cnf(c_767,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1616,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
    | k10_relat_1(sK4,sK3) != X0
    | k10_relat_1(sK4,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1618,plain,
    ( r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k10_relat_1(sK4,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1468,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
    | r1_xboole_0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1465,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_504,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_505,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_28,plain,
    ( k1_xboole_0 = k10_relat_1(sK4,sK3)
    | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20249,c_7359,c_7283,c_4785,c_4226,c_2218,c_2172,c_1618,c_1468,c_1465,c_505,c_73,c_24,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.56/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.49  
% 7.56/1.49  ------  iProver source info
% 7.56/1.49  
% 7.56/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.49  git: non_committed_changes: false
% 7.56/1.49  git: last_make_outside_of_git: false
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  ------ Parsing...
% 7.56/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  ------ Proving...
% 7.56/1.49  ------ Problem Properties 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  clauses                                 25
% 7.56/1.49  conjectures                             2
% 7.56/1.49  EPR                                     6
% 7.56/1.49  Horn                                    22
% 7.56/1.49  unary                                   4
% 7.56/1.49  binary                                  16
% 7.56/1.49  lits                                    52
% 7.56/1.49  lits eq                                 8
% 7.56/1.49  fd_pure                                 0
% 7.56/1.49  fd_pseudo                               0
% 7.56/1.49  fd_cond                                 1
% 7.56/1.49  fd_pseudo_cond                          1
% 7.56/1.49  AC symbols                              0
% 7.56/1.49  
% 7.56/1.49  ------ Input Options Time Limit: Unbounded
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  Current options:
% 7.56/1.49  ------ 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS status Theorem for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  fof(f3,axiom,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f16,plain,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(rectify,[],[f3])).
% 7.56/1.49  
% 7.56/1.49  fof(f18,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(ennf_transformation,[],[f16])).
% 7.56/1.49  
% 7.56/1.49  fof(f30,plain,(
% 7.56/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f31,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).
% 7.56/1.49  
% 7.56/1.49  fof(f51,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f31])).
% 7.56/1.49  
% 7.56/1.49  fof(f13,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f26,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(ennf_transformation,[],[f13])).
% 7.56/1.49  
% 7.56/1.49  fof(f27,plain,(
% 7.56/1.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(flattening,[],[f26])).
% 7.56/1.49  
% 7.56/1.49  fof(f70,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f27])).
% 7.56/1.49  
% 7.56/1.49  fof(f14,conjecture,(
% 7.56/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f15,negated_conjecture,(
% 7.56/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    inference(negated_conjecture,[],[f14])).
% 7.56/1.49  
% 7.56/1.49  fof(f28,plain,(
% 7.56/1.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.56/1.49    inference(ennf_transformation,[],[f15])).
% 7.56/1.49  
% 7.56/1.49  fof(f42,plain,(
% 7.56/1.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.56/1.49    inference(nnf_transformation,[],[f28])).
% 7.56/1.49  
% 7.56/1.49  fof(f43,plain,(
% 7.56/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.56/1.49    inference(flattening,[],[f42])).
% 7.56/1.49  
% 7.56/1.49  fof(f44,plain,(
% 7.56/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f45,plain,(
% 7.56/1.49    (~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)) & (r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)) & v1_relat_1(sK4)),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f44])).
% 7.56/1.49  
% 7.56/1.49  fof(f71,plain,(
% 7.56/1.49    v1_relat_1(sK4)),
% 7.56/1.49    inference(cnf_transformation,[],[f45])).
% 7.56/1.49  
% 7.56/1.49  fof(f11,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f24,plain,(
% 7.56/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(ennf_transformation,[],[f11])).
% 7.56/1.49  
% 7.56/1.49  fof(f38,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(nnf_transformation,[],[f24])).
% 7.56/1.49  
% 7.56/1.49  fof(f39,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(rectify,[],[f38])).
% 7.56/1.49  
% 7.56/1.49  fof(f40,plain,(
% 7.56/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f41,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.56/1.49  
% 7.56/1.49  fof(f67,plain,(
% 7.56/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f41])).
% 7.56/1.49  
% 7.56/1.49  fof(f9,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f22,plain,(
% 7.56/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(ennf_transformation,[],[f9])).
% 7.56/1.49  
% 7.56/1.49  fof(f34,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(nnf_transformation,[],[f22])).
% 7.56/1.49  
% 7.56/1.49  fof(f35,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(rectify,[],[f34])).
% 7.56/1.49  
% 7.56/1.49  fof(f36,plain,(
% 7.56/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f37,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.56/1.49  
% 7.56/1.49  fof(f60,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f37])).
% 7.56/1.49  
% 7.56/1.49  fof(f72,plain,(
% 7.56/1.49    r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 = k10_relat_1(sK4,sK3)),
% 7.56/1.49    inference(cnf_transformation,[],[f45])).
% 7.56/1.49  
% 7.56/1.49  fof(f1,axiom,(
% 7.56/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f29,plain,(
% 7.56/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(nnf_transformation,[],[f1])).
% 7.56/1.49  
% 7.56/1.49  fof(f46,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f29])).
% 7.56/1.49  
% 7.56/1.49  fof(f8,axiom,(
% 7.56/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f58,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f8])).
% 7.56/1.49  
% 7.56/1.49  fof(f75,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(definition_unfolding,[],[f46,f58])).
% 7.56/1.49  
% 7.56/1.49  fof(f12,axiom,(
% 7.56/1.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f25,plain,(
% 7.56/1.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.56/1.49    inference(ennf_transformation,[],[f12])).
% 7.56/1.49  
% 7.56/1.49  fof(f68,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f25])).
% 7.56/1.49  
% 7.56/1.49  fof(f76,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.56/1.49    inference(definition_unfolding,[],[f68,f58])).
% 7.56/1.49  
% 7.56/1.49  fof(f73,plain,(
% 7.56/1.49    ~r1_xboole_0(k2_relat_1(sK4),sK3) | k1_xboole_0 != k10_relat_1(sK4,sK3)),
% 7.56/1.49    inference(cnf_transformation,[],[f45])).
% 7.56/1.49  
% 7.56/1.49  fof(f6,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f19,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.56/1.49    inference(ennf_transformation,[],[f6])).
% 7.56/1.49  
% 7.56/1.49  fof(f20,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.56/1.49    inference(flattening,[],[f19])).
% 7.56/1.49  
% 7.56/1.49  fof(f56,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f20])).
% 7.56/1.49  
% 7.56/1.49  fof(f5,axiom,(
% 7.56/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f55,plain,(
% 7.56/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f5])).
% 7.56/1.49  
% 7.56/1.49  fof(f4,axiom,(
% 7.56/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f32,plain,(
% 7.56/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.49    inference(nnf_transformation,[],[f4])).
% 7.56/1.49  
% 7.56/1.49  fof(f33,plain,(
% 7.56/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.49    inference(flattening,[],[f32])).
% 7.56/1.49  
% 7.56/1.49  fof(f52,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.56/1.49    inference(cnf_transformation,[],[f33])).
% 7.56/1.49  
% 7.56/1.49  fof(f78,plain,(
% 7.56/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.56/1.49    inference(equality_resolution,[],[f52])).
% 7.56/1.49  
% 7.56/1.49  fof(f50,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f31])).
% 7.56/1.49  
% 7.56/1.49  fof(f66,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f41])).
% 7.56/1.49  
% 7.56/1.49  fof(f7,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f21,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 7.56/1.49    inference(ennf_transformation,[],[f7])).
% 7.56/1.49  
% 7.56/1.49  fof(f57,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f21])).
% 7.56/1.49  
% 7.56/1.49  fof(f2,axiom,(
% 7.56/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f17,plain,(
% 7.56/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.56/1.49    inference(ennf_transformation,[],[f2])).
% 7.56/1.49  
% 7.56/1.49  fof(f48,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f17])).
% 7.56/1.49  
% 7.56/1.49  fof(f49,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f31])).
% 7.56/1.49  
% 7.56/1.49  fof(f10,axiom,(
% 7.56/1.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f23,plain,(
% 7.56/1.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f10])).
% 7.56/1.49  
% 7.56/1.49  fof(f63,plain,(
% 7.56/1.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f23])).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14420,plain,
% 7.56/1.49      ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),X0)
% 7.56/1.49      | ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 7.56/1.49      | ~ r1_xboole_0(k10_relat_1(sK4,sK3),X0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_20249,plain,
% 7.56/1.49      ( ~ r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 7.56/1.49      | ~ r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_14420]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_22,plain,
% 7.56/1.49      ( r2_hidden(X0,k2_relat_1(X1))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.56/1.49      | ~ v1_relat_1(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_26,negated_conjecture,
% 7.56/1.49      ( v1_relat_1(sK4) ),
% 7.56/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_410,plain,
% 7.56/1.49      ( r2_hidden(X0,k2_relat_1(X1))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.56/1.49      | sK4 != X1 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_411,plain,
% 7.56/1.49      ( r2_hidden(X0,k2_relat_1(sK4))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_410]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_17,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1)
% 7.56/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.56/1.49      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.56/1.49      | ~ v1_relat_1(X3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_358,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1)
% 7.56/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.56/1.49      | ~ r2_hidden(X0,k2_relat_1(X3))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.56/1.49      | sK4 != X3 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_359,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1)
% 7.56/1.49      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 7.56/1.49      | ~ r2_hidden(X0,k2_relat_1(sK4))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_358]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_420,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1)
% 7.56/1.49      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 7.56/1.49      inference(backward_subsumption_resolution,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_411,c_359]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1757,plain,
% 7.56/1.49      ( r2_hidden(X0,k10_relat_1(sK4,sK3))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X0,sK0(k2_relat_1(sK4),sK3)),sK4)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_420]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7359,plain,
% 7.56/1.49      ( r2_hidden(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),k10_relat_1(sK4,sK3))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1757]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.56/1.49      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.56/1.49      | ~ v1_relat_1(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_474,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.56/1.49      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.56/1.49      | sK4 != X1 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_475,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 7.56/1.49      | r2_hidden(k4_tarski(sK1(X0,X1,sK4),X0),sK4) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_474]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7283,plain,
% 7.56/1.49      ( r2_hidden(k4_tarski(sK1(sK0(k2_relat_1(sK4),sK3),k1_relat_1(sK4),sK4),sK0(k2_relat_1(sK4),sK3)),sK4)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4))) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_475]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_770,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.49      theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1780,plain,
% 7.56/1.49      ( r2_hidden(X0,X1)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 7.56/1.49      | X0 != sK0(k2_relat_1(sK4),sK3)
% 7.56/1.49      | X1 != k2_relat_1(sK4) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_770]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2622,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),X0)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 7.56/1.49      | X0 != k2_relat_1(sK4)
% 7.56/1.49      | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1780]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4785,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k9_relat_1(sK4,k1_relat_1(sK4)))
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 7.56/1.49      | k9_relat_1(sK4,k1_relat_1(sK4)) != k2_relat_1(sK4)
% 7.56/1.49      | sK0(k2_relat_1(sK4),sK3) != sK0(k2_relat_1(sK4),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_2622]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_25,negated_conjecture,
% 7.56/1.49      ( r1_xboole_0(k2_relat_1(sK4),sK3)
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1349,plain,
% 7.56/1.49      ( k1_xboole_0 = k10_relat_1(sK4,sK3)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.56/1.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1360,plain,
% 7.56/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.56/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1552,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 7.56/1.49      | k1_setfam_1(k2_tarski(k2_relat_1(sK4),sK3)) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1349,c_1360]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_21,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0)
% 7.56/1.49      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_498,plain,
% 7.56/1.49      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 7.56/1.49      | sK4 != X0 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_499,plain,
% 7.56/1.49      ( k10_relat_1(sK4,k1_setfam_1(k2_tarski(k2_relat_1(sK4),X0))) = k10_relat_1(sK4,X0) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_498]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2257,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK4,k1_xboole_0) = k10_relat_1(sK4,sK3) ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1552,c_499]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_24,negated_conjecture,
% 7.56/1.49      ( ~ r1_xboole_0(k2_relat_1(sK4),sK3)
% 7.56/1.49      | k1_xboole_0 != k10_relat_1(sK4,sK3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1350,plain,
% 7.56/1.49      ( k1_xboole_0 != k10_relat_1(sK4,sK3)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4223,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2257,c_1350]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_29,plain,
% 7.56/1.49      ( k1_xboole_0 != k10_relat_1(sK4,sK3)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10,plain,
% 7.56/1.49      ( ~ r1_tarski(X0,X1)
% 7.56/1.49      | ~ r1_tarski(X0,X2)
% 7.56/1.49      | ~ r1_xboole_0(X1,X2)
% 7.56/1.49      | k1_xboole_0 = X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_70,plain,
% 7.56/1.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.56/1.49      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.56/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_9,plain,
% 7.56/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_73,plain,
% 7.56/1.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8,plain,
% 7.56/1.49      ( r1_tarski(X0,X0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_76,plain,
% 7.56/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_766,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1529,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) != X0
% 7.56/1.49      | k1_xboole_0 != X0
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK4,sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_766]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1530,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) != k1_xboole_0
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK4,sK3)
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1529]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4,plain,
% 7.56/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1357,plain,
% 7.56/1.49      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.56/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_18,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.56/1.49      | r2_hidden(sK2(X0,X2,X1),X2)
% 7.56/1.49      | ~ v1_relat_1(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_450,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.56/1.49      | r2_hidden(sK2(X0,X2,X1),X2)
% 7.56/1.49      | sK4 != X1 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_451,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 7.56/1.49      | r2_hidden(sK2(X0,X1,sK4),X1) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_450]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1342,plain,
% 7.56/1.49      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 7.56/1.49      | r2_hidden(sK2(X0,X1,sK4),X1) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1353,plain,
% 7.56/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_tarski(X0,X2),X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1351,plain,
% 7.56/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.56/1.49      | r1_xboole_0(k2_tarski(X0,X2),X1) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1702,plain,
% 7.56/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1353,c_1351]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2249,plain,
% 7.56/1.49      ( r2_hidden(X0,k10_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1342,c_1702]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3670,plain,
% 7.56/1.49      ( r1_xboole_0(X0,k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1357,c_2249]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1354,plain,
% 7.56/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1352,plain,
% 7.56/1.49      ( k1_xboole_0 = X0
% 7.56/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.56/1.49      | r1_tarski(X0,X2) != iProver_top
% 7.56/1.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1931,plain,
% 7.56/1.49      ( k1_xboole_0 = X0
% 7.56/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.56/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1354,c_1352]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2381,plain,
% 7.56/1.49      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1354,c_1931]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3692,plain,
% 7.56/1.49      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3670,c_2381]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4226,plain,
% 7.56/1.49      ( r1_xboole_0(k2_relat_1(sK4),sK3) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_4223,c_29,c_70,c_73,c_76,c_1530,c_3692]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_765,plain,( X0 = X0 ),theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2218,plain,
% 7.56/1.49      ( sK0(k2_relat_1(sK4),sK3) = sK0(k2_relat_1(sK4),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_765]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1359,plain,
% 7.56/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 7.56/1.49      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1473,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 7.56/1.49      | r1_xboole_0(sK3,k2_relat_1(sK4)) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1349,c_1359]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2172,plain,
% 7.56/1.49      ( k10_relat_1(sK4,sK3) = k1_xboole_0
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1473,c_1359]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_767,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.49      theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1616,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.56/1.49      | r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
% 7.56/1.49      | k10_relat_1(sK4,sK3) != X0
% 7.56/1.49      | k10_relat_1(sK4,sK3) != X1 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_767]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1618,plain,
% 7.56/1.49      ( r1_xboole_0(k10_relat_1(sK4,sK3),k10_relat_1(sK4,sK3))
% 7.56/1.49      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.56/1.49      | k10_relat_1(sK4,sK3) != k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1616]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_5,plain,
% 7.56/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1468,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),k2_relat_1(sK4))
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1465,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK4),sK3),sK3)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0)
% 7.56/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_504,plain,
% 7.56/1.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK4 != X0 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_505,plain,
% 7.56/1.49      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_504]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_28,plain,
% 7.56/1.49      ( k1_xboole_0 = k10_relat_1(sK4,sK3)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(contradiction,plain,
% 7.56/1.49      ( $false ),
% 7.56/1.49      inference(minisat,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_20249,c_7359,c_7283,c_4785,c_4226,c_2218,c_2172,
% 7.56/1.49                 c_1618,c_1468,c_1465,c_505,c_73,c_24,c_28]) ).
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  ------                               Statistics
% 7.56/1.49  
% 7.56/1.49  ------ Selected
% 7.56/1.49  
% 7.56/1.49  total_time:                             0.557
% 7.56/1.49  
%------------------------------------------------------------------------------
