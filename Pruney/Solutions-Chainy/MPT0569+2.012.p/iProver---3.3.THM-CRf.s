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
% DateTime   : Thu Dec  3 11:47:29 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 753 expanded)
%              Number of clauses        :   74 ( 283 expanded)
%              Number of leaves         :   21 ( 184 expanded)
%              Depth                    :   26
%              Number of atoms          :  451 (2896 expanded)
%              Number of equality atoms :  141 ( 934 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 != k10_relat_1(sK11,sK10) )
      & ( r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 = k10_relat_1(sK11,sK10) )
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 != k10_relat_1(sK11,sK10) )
    & ( r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 = k10_relat_1(sK11,sK10) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f49,f50])).

fof(f85,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f42,f41,f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).

fof(f70,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_545,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_25455,plain,
    ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_548,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9245,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | X1 != k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_25454,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | X0 != k10_relat_1(sK11,sK10)
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_9245])).

cnf(c_25457,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_25454])).

cnf(c_546,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2650,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_546,c_545])).

cnf(c_30,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3284,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2650,c_30])).

cnf(c_3297,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k1_xboole_0
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(resolution,[status(thm)],[c_3284,c_546])).

cnf(c_3366,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != X1
    | X1 != k1_xboole_0
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(resolution,[status(thm)],[c_3297,c_546])).

cnf(c_27,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3830,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k2_relat_1(k1_xboole_0)
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(resolution,[status(thm)],[c_3366,c_27])).

cnf(c_29,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2648,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k10_relat_1(sK11,sK10)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_546,c_30])).

cnf(c_3372,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(resolution,[status(thm)],[c_3297,c_2648])).

cnf(c_564,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1644,plain,
    ( k10_relat_1(sK11,sK10) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1645,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_3375,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_564,c_1645])).

cnf(c_20,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1169,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK6(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1178,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1177,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1514,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1177])).

cnf(c_3411,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1514])).

cnf(c_3430,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3411,c_27])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1166,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1164,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1162,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10)
    | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1183,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2595,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1183])).

cnf(c_3084,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_2595])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3205,plain,
    ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3084,c_32])).

cnf(c_3206,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_3205])).

cnf(c_3214,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_3206])).

cnf(c_3975,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3214,c_32])).

cnf(c_3976,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3975])).

cnf(c_3990,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3430,c_3976])).

cnf(c_4362,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_29,c_564,c_1645,c_3990])).

cnf(c_4380,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k10_relat_1(sK11,sK10) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(resolution,[status(thm)],[c_4362,c_2648])).

cnf(c_4385,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_564,c_1645,c_3990])).

cnf(c_4709,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4385,c_29])).

cnf(c_3364,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 = k10_relat_1(sK11,sK10)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3297,c_2650])).

cnf(c_4722,plain,
    ( X0 = k10_relat_1(sK11,sK10)
    | X0 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4709,c_3364])).

cnf(c_549,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5330,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k10_relat_1(sK11,sK10))
    | X0 != X2
    | X1 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4722,c_549])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1486,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_1798,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_22,c_1486])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1898,plain,
    ( r1_xboole_0(k2_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_1798,c_8])).

cnf(c_7883,plain,
    ( r1_xboole_0(X0,X1)
    | X0 != k2_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5330,c_1898])).

cnf(c_4723,plain,
    ( X0 != k1_xboole_0
    | k10_relat_1(sK11,sK10) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4709,c_3297])).

cnf(c_11808,plain,
    ( r1_xboole_0(k10_relat_1(sK11,sK10),X0)
    | X0 != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7883,c_4723])).

cnf(c_11814,plain,
    ( r1_xboole_0(k10_relat_1(sK11,sK10),k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11808])).

cnf(c_9258,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK11,sK10),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9260,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK11,sK10),k1_xboole_0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9258])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1984,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6394,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),sK10)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_1583,plain,
    ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1448,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1445,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),sK10) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25455,c_25457,c_11814,c_9260,c_6394,c_3990,c_3375,c_1583,c_1448,c_1445,c_564,c_27,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:43:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.79/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.48  
% 7.79/1.48  ------  iProver source info
% 7.79/1.48  
% 7.79/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.48  git: non_committed_changes: false
% 7.79/1.48  git: last_make_outside_of_git: false
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  ------ Parsing...
% 7.79/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.48  ------ Proving...
% 7.79/1.48  ------ Problem Properties 
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  clauses                                 31
% 7.79/1.48  conjectures                             3
% 7.79/1.48  EPR                                     3
% 7.79/1.48  Horn                                    22
% 7.79/1.48  unary                                   4
% 7.79/1.48  binary                                  11
% 7.79/1.48  lits                                    80
% 7.79/1.48  lits eq                                 12
% 7.79/1.48  fd_pure                                 0
% 7.79/1.48  fd_pseudo                               0
% 7.79/1.48  fd_cond                                 0
% 7.79/1.48  fd_pseudo_cond                          8
% 7.79/1.48  AC symbols                              0
% 7.79/1.48  
% 7.79/1.48  ------ Input Options Time Limit: Unbounded
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  Current options:
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ Proving...
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS status Theorem for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  fof(f13,conjecture,(
% 7.79/1.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f14,negated_conjecture,(
% 7.79/1.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.79/1.48    inference(negated_conjecture,[],[f13])).
% 7.79/1.48  
% 7.79/1.48  fof(f22,plain,(
% 7.79/1.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.79/1.48    inference(ennf_transformation,[],[f14])).
% 7.79/1.48  
% 7.79/1.48  fof(f48,plain,(
% 7.79/1.48    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.79/1.48    inference(nnf_transformation,[],[f22])).
% 7.79/1.48  
% 7.79/1.48  fof(f49,plain,(
% 7.79/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.79/1.48    inference(flattening,[],[f48])).
% 7.79/1.48  
% 7.79/1.48  fof(f50,plain,(
% 7.79/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f51,plain,(
% 7.79/1.48    (~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11)),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f49,f50])).
% 7.79/1.48  
% 7.79/1.48  fof(f85,plain,(
% 7.79/1.48    r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)),
% 7.79/1.48    inference(cnf_transformation,[],[f51])).
% 7.79/1.48  
% 7.79/1.48  fof(f12,axiom,(
% 7.79/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f83,plain,(
% 7.79/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.79/1.48    inference(cnf_transformation,[],[f12])).
% 7.79/1.48  
% 7.79/1.48  fof(f86,plain,(
% 7.79/1.48    ~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)),
% 7.79/1.48    inference(cnf_transformation,[],[f51])).
% 7.79/1.48  
% 7.79/1.48  fof(f10,axiom,(
% 7.79/1.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f38,plain,(
% 7.79/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.79/1.48    inference(nnf_transformation,[],[f10])).
% 7.79/1.48  
% 7.79/1.48  fof(f39,plain,(
% 7.79/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.79/1.48    inference(rectify,[],[f38])).
% 7.79/1.48  
% 7.79/1.48  fof(f42,plain,(
% 7.79/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f41,plain,(
% 7.79/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f40,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f43,plain,(
% 7.79/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f42,f41,f40])).
% 7.79/1.48  
% 7.79/1.48  fof(f76,plain,(
% 7.79/1.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f43])).
% 7.79/1.48  
% 7.79/1.48  fof(f4,axiom,(
% 7.79/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f63,plain,(
% 7.79/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f4])).
% 7.79/1.48  
% 7.79/1.48  fof(f7,axiom,(
% 7.79/1.48    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f19,plain,(
% 7.79/1.48    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 7.79/1.48    inference(ennf_transformation,[],[f7])).
% 7.79/1.48  
% 7.79/1.48  fof(f66,plain,(
% 7.79/1.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f19])).
% 7.79/1.48  
% 7.79/1.48  fof(f11,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f21,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.79/1.48    inference(ennf_transformation,[],[f11])).
% 7.79/1.48  
% 7.79/1.48  fof(f44,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.79/1.48    inference(nnf_transformation,[],[f21])).
% 7.79/1.48  
% 7.79/1.48  fof(f45,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.79/1.48    inference(rectify,[],[f44])).
% 7.79/1.48  
% 7.79/1.48  fof(f46,plain,(
% 7.79/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f47,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f80,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f47])).
% 7.79/1.48  
% 7.79/1.48  fof(f78,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f47])).
% 7.79/1.48  
% 7.79/1.48  fof(f2,axiom,(
% 7.79/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f15,plain,(
% 7.79/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.79/1.48    inference(rectify,[],[f2])).
% 7.79/1.48  
% 7.79/1.48  fof(f17,plain,(
% 7.79/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.79/1.48    inference(ennf_transformation,[],[f15])).
% 7.79/1.48  
% 7.79/1.48  fof(f28,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f29,plain,(
% 7.79/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).
% 7.79/1.48  
% 7.79/1.48  fof(f60,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f29])).
% 7.79/1.48  
% 7.79/1.48  fof(f84,plain,(
% 7.79/1.48    v1_relat_1(sK11)),
% 7.79/1.48    inference(cnf_transformation,[],[f51])).
% 7.79/1.48  
% 7.79/1.48  fof(f74,plain,(
% 7.79/1.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.79/1.48    inference(cnf_transformation,[],[f43])).
% 7.79/1.48  
% 7.79/1.48  fof(f104,plain,(
% 7.79/1.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.79/1.48    inference(equality_resolution,[],[f74])).
% 7.79/1.48  
% 7.79/1.48  fof(f58,plain,(
% 7.79/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f29])).
% 7.79/1.48  
% 7.79/1.48  fof(f9,axiom,(
% 7.79/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f20,plain,(
% 7.79/1.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(ennf_transformation,[],[f9])).
% 7.79/1.48  
% 7.79/1.48  fof(f32,plain,(
% 7.79/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(nnf_transformation,[],[f20])).
% 7.79/1.48  
% 7.79/1.48  fof(f33,plain,(
% 7.79/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(rectify,[],[f32])).
% 7.79/1.48  
% 7.79/1.48  fof(f36,plain,(
% 7.79/1.48    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f35,plain,(
% 7.79/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f34,plain,(
% 7.79/1.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f37,plain,(
% 7.79/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).
% 7.79/1.48  
% 7.79/1.48  fof(f70,plain,(
% 7.79/1.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f37])).
% 7.79/1.48  
% 7.79/1.48  fof(f100,plain,(
% 7.79/1.48    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(equality_resolution,[],[f70])).
% 7.79/1.48  
% 7.79/1.48  fof(f59,plain,(
% 7.79/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f29])).
% 7.79/1.48  
% 7.79/1.48  cnf(c_545,plain,( X0 = X0 ),theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25455,plain,
% 7.79/1.48      ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_545]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_548,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.79/1.48      theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9245,plain,
% 7.79/1.48      ( r2_hidden(X0,X1)
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.79/1.48      | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 7.79/1.48      | X1 != k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_548]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25454,plain,
% 7.79/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.79/1.48      | X0 != k10_relat_1(sK11,sK10)
% 7.79/1.48      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_9245]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25457,plain,
% 7.79/1.48      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.79/1.48      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
% 7.79/1.48      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 7.79/1.48      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_25454]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_546,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2650,plain,
% 7.79/1.48      ( X0 != X1 | X1 = X0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_546,c_545]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_30,negated_conjecture,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3284,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_2650,c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3297,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | X0 != k1_xboole_0
% 7.79/1.48      | k10_relat_1(sK11,sK10) = X0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_3284,c_546]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3366,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | X0 != X1
% 7.79/1.48      | X1 != k1_xboole_0
% 7.79/1.48      | k10_relat_1(sK11,sK10) = X0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_3297,c_546]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_27,plain,
% 7.79/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3830,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | X0 != k2_relat_1(k1_xboole_0)
% 7.79/1.48      | k10_relat_1(sK11,sK10) = X0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_3366,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_29,negated_conjecture,
% 7.79/1.48      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2648,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | X0 != k10_relat_1(sK11,sK10)
% 7.79/1.48      | k1_xboole_0 = X0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_546,c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3372,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_3297,c_2648]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_564,plain,
% 7.79/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_545]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1644,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) != X0
% 7.79/1.48      | k1_xboole_0 != X0
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_546]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1645,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10)
% 7.79/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1644]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3375,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3372,c_564,c_1645]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_20,plain,
% 7.79/1.48      ( r2_hidden(sK6(X0,X1),X1)
% 7.79/1.48      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
% 7.79/1.48      | k2_relat_1(X0) = X1 ),
% 7.79/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1169,plain,
% 7.79/1.48      ( k2_relat_1(X0) = X1
% 7.79/1.48      | r2_hidden(sK6(X0,X1),X1) = iProver_top
% 7.79/1.48      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11,plain,
% 7.79/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1178,plain,
% 7.79/1.48      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_12,plain,
% 7.79/1.48      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1177,plain,
% 7.79/1.48      ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
% 7.79/1.48      | r2_hidden(X0,X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1514,plain,
% 7.79/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1178,c_1177]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3411,plain,
% 7.79/1.48      ( k2_relat_1(k1_xboole_0) = X0
% 7.79/1.48      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1169,c_1514]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3430,plain,
% 7.79/1.48      ( k1_xboole_0 = X0
% 7.79/1.48      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3411,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_24,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.79/1.48      | r2_hidden(sK9(X0,X2,X1),X2)
% 7.79/1.48      | ~ v1_relat_1(X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1166,plain,
% 7.79/1.48      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.79/1.48      | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_26,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.79/1.48      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
% 7.79/1.48      | ~ v1_relat_1(X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1164,plain,
% 7.79/1.48      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 7.79/1.48      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1162,plain,
% 7.79/1.48      ( k1_xboole_0 = k10_relat_1(sK11,sK10)
% 7.79/1.48      | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6,plain,
% 7.79/1.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1183,plain,
% 7.79/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 7.79/1.48      | r2_hidden(X2,X1) != iProver_top
% 7.79/1.48      | r2_hidden(X2,X0) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2595,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.79/1.48      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 7.79/1.48      | r2_hidden(X0,sK10) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1162,c_1183]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3084,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.79/1.48      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 7.79/1.48      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 7.79/1.48      | v1_relat_1(sK11) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1164,c_2595]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_31,negated_conjecture,
% 7.79/1.48      ( v1_relat_1(sK11) ),
% 7.79/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_32,plain,
% 7.79/1.48      ( v1_relat_1(sK11) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3205,plain,
% 7.79/1.48      ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 7.79/1.48      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 7.79/1.48      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3084,c_32]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3206,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.79/1.48      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 7.79/1.48      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_3205]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3214,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.79/1.48      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK11) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1166,c_3206]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3975,plain,
% 7.79/1.48      ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 7.79/1.48      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3214,c_32]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3976,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.79/1.48      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_3975]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3990,plain,
% 7.79/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3430,c_3976]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4362,plain,
% 7.79/1.48      ( X0 != k2_relat_1(k1_xboole_0) | k10_relat_1(sK11,sK10) = X0 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3830,c_29,c_564,c_1645,c_3990]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4380,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | k10_relat_1(sK11,sK10) != k2_relat_1(k1_xboole_0)
% 7.79/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_4362,c_2648]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4385,plain,
% 7.79/1.48      ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_4380,c_564,c_1645,c_3990]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4709,plain,
% 7.79/1.48      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
% 7.79/1.48      inference(backward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_4385,c_29]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3364,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | X0 = k10_relat_1(sK11,sK10)
% 7.79/1.48      | X0 != k1_xboole_0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_3297,c_2650]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4722,plain,
% 7.79/1.48      ( X0 = k10_relat_1(sK11,sK10) | X0 != k1_xboole_0 ),
% 7.79/1.48      inference(backward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_4709,c_3364]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_549,plain,
% 7.79/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.79/1.48      theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5330,plain,
% 7.79/1.48      ( r1_xboole_0(X0,X1)
% 7.79/1.48      | ~ r1_xboole_0(X2,k10_relat_1(sK11,sK10))
% 7.79/1.48      | X0 != X2
% 7.79/1.48      | X1 != k1_xboole_0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_4722,c_549]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_22,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.79/1.48      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1486,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1798,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_22,c_1486]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_8,plain,
% 7.79/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1898,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(k1_xboole_0),X0) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_1798,c_8]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7883,plain,
% 7.79/1.48      ( r1_xboole_0(X0,X1)
% 7.79/1.48      | X0 != k2_relat_1(k1_xboole_0)
% 7.79/1.48      | X1 != k1_xboole_0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_5330,c_1898]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_4723,plain,
% 7.79/1.48      ( X0 != k1_xboole_0 | k10_relat_1(sK11,sK10) = X0 ),
% 7.79/1.48      inference(backward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_4709,c_3297]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11808,plain,
% 7.79/1.48      ( r1_xboole_0(k10_relat_1(sK11,sK10),X0)
% 7.79/1.48      | X0 != k1_xboole_0
% 7.79/1.48      | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_7883,c_4723]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11814,plain,
% 7.79/1.48      ( r1_xboole_0(k10_relat_1(sK11,sK10),k1_xboole_0)
% 7.79/1.48      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_11808]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9258,plain,
% 7.79/1.48      ( ~ r1_xboole_0(k10_relat_1(sK11,sK10),X0)
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9260,plain,
% 7.79/1.48      ( ~ r1_xboole_0(k10_relat_1(sK11,sK10),k1_xboole_0)
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.79/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_9258]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_16,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,X1)
% 7.79/1.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.79/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.79/1.48      | ~ v1_relat_1(X3) ),
% 7.79/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1984,plain,
% 7.79/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
% 7.79/1.48      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.79/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
% 7.79/1.48      | ~ v1_relat_1(sK11) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6394,plain,
% 7.79/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10))
% 7.79/1.48      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.79/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),sK10)
% 7.79/1.48      | ~ v1_relat_1(sK11) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1984]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1583,plain,
% 7.79/1.48      ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.79/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1448,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7,plain,
% 7.79/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1445,plain,
% 7.79/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.79/1.48      | r2_hidden(sK1(k2_relat_1(sK11),sK10),sK10) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(contradiction,plain,
% 7.79/1.48      ( $false ),
% 7.79/1.48      inference(minisat,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_25455,c_25457,c_11814,c_9260,c_6394,c_3990,c_3375,
% 7.79/1.48                 c_1583,c_1448,c_1445,c_564,c_27,c_29,c_31]) ).
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  ------                               Statistics
% 7.79/1.48  
% 7.79/1.48  ------ Selected
% 7.79/1.48  
% 7.79/1.48  total_time:                             0.721
% 7.79/1.48  
%------------------------------------------------------------------------------
