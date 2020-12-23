%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:29 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 432 expanded)
%              Number of clauses        :   53 ( 116 expanded)
%              Number of leaves         :   21 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  473 (1671 expanded)
%              Number of equality atoms :  109 ( 441 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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
    inference(rectify,[],[f2])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f7,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f63,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

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

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 != k10_relat_1(sK11,sK10) )
    & ( r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 = k10_relat_1(sK11,sK10) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f46,f47])).

fof(f76,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f78,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f75,f60])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_388,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_22875,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_7198,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7200,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),k1_xboole_0)))
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7198])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK11 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK11) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_4094,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,k2_relat_1(sK11)))
    | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_5680,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_4094])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_223,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_397,plain,
    ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
    | k10_relat_1(sK11,sK10) != k1_xboole_0
    | k2_relat_1(sK11) != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_223])).

cnf(c_398,plain,
    ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))
    | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1210,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_399,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1217,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_533,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,X1))
    | r2_hidden(sK9(X0,X1,sK11),X1) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_1202,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_27,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_225,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | k10_relat_1(sK11,sK10) = k1_xboole_0
    | k2_relat_1(sK11) != X1
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_225])).

cnf(c_408,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1209,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2669,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1209])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_440,plain,
    ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_441,plain,
    ( k10_relat_1(sK11,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X0))) = k10_relat_1(sK11,X0) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_2673,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_441])).

cnf(c_3164,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1217,c_2673])).

cnf(c_3679,plain,
    ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_399,c_3164])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1213,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1205,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK11,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2958,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1205])).

cnf(c_4804,plain,
    ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X1))) != iProver_top
    | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_2958])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1218,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4835,plain,
    ( r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X1))) != iProver_top
    | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4804,c_1218])).

cnf(c_4843,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_4835])).

cnf(c_4893,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4843,c_3164])).

cnf(c_4936,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4893])).

cnf(c_4112,plain,
    ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1648,plain,
    ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11))
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22875,c_7200,c_5680,c_4936,c_4112,c_3164,c_1648,c_398])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:54:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.83/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.48  
% 7.83/1.48  ------  iProver source info
% 7.83/1.48  
% 7.83/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.48  git: non_committed_changes: false
% 7.83/1.48  git: last_make_outside_of_git: false
% 7.83/1.48  
% 7.83/1.48  ------ 
% 7.83/1.48  ------ Parsing...
% 7.83/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.48  ------ Proving...
% 7.83/1.48  ------ Problem Properties 
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  clauses                                 27
% 7.83/1.48  conjectures                             0
% 7.83/1.48  EPR                                     0
% 7.83/1.48  Horn                                    21
% 7.83/1.48  unary                                   3
% 7.83/1.48  binary                                  14
% 7.83/1.48  lits                                    63
% 7.83/1.48  lits eq                                 15
% 7.83/1.48  fd_pure                                 0
% 7.83/1.48  fd_pseudo                               0
% 7.83/1.48  fd_cond                                 1
% 7.83/1.48  fd_pseudo_cond                          8
% 7.83/1.48  AC symbols                              0
% 7.83/1.48  
% 7.83/1.48  ------ Input Options Time Limit: Unbounded
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  ------ 
% 7.83/1.48  Current options:
% 7.83/1.48  ------ 
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  ------ Proving...
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  % SZS status Theorem for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  fof(f2,axiom,(
% 7.83/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f13,plain,(
% 7.83/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.83/1.48    inference(rectify,[],[f2])).
% 7.83/1.48  
% 7.83/1.48  fof(f14,plain,(
% 7.83/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.83/1.48    inference(ennf_transformation,[],[f13])).
% 7.83/1.48  
% 7.83/1.48  fof(f25,plain,(
% 7.83/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f26,plain,(
% 7.83/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).
% 7.83/1.48  
% 7.83/1.48  fof(f56,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f26])).
% 7.83/1.48  
% 7.83/1.48  fof(f6,axiom,(
% 7.83/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f60,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f6])).
% 7.83/1.48  
% 7.83/1.48  fof(f85,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.83/1.48    inference(definition_unfolding,[],[f56,f60])).
% 7.83/1.48  
% 7.83/1.48  fof(f5,axiom,(
% 7.83/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f59,plain,(
% 7.83/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f5])).
% 7.83/1.48  
% 7.83/1.48  fof(f1,axiom,(
% 7.83/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f20,plain,(
% 7.83/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.83/1.48    inference(nnf_transformation,[],[f1])).
% 7.83/1.48  
% 7.83/1.48  fof(f21,plain,(
% 7.83/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.83/1.48    inference(flattening,[],[f20])).
% 7.83/1.48  
% 7.83/1.48  fof(f22,plain,(
% 7.83/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.83/1.48    inference(rectify,[],[f21])).
% 7.83/1.48  
% 7.83/1.48  fof(f23,plain,(
% 7.83/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f24,plain,(
% 7.83/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 7.83/1.48  
% 7.83/1.48  fof(f51,plain,(
% 7.83/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.83/1.48    inference(cnf_transformation,[],[f24])).
% 7.83/1.48  
% 7.83/1.48  fof(f82,plain,(
% 7.83/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 7.83/1.48    inference(definition_unfolding,[],[f51,f60])).
% 7.83/1.48  
% 7.83/1.48  fof(f89,plain,(
% 7.83/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.83/1.48    inference(equality_resolution,[],[f82])).
% 7.83/1.48  
% 7.83/1.48  fof(f7,axiom,(
% 7.83/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f16,plain,(
% 7.83/1.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 7.83/1.48    inference(ennf_transformation,[],[f7])).
% 7.83/1.48  
% 7.83/1.48  fof(f29,plain,(
% 7.83/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.83/1.48    inference(nnf_transformation,[],[f16])).
% 7.83/1.48  
% 7.83/1.48  fof(f30,plain,(
% 7.83/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.83/1.48    inference(rectify,[],[f29])).
% 7.83/1.48  
% 7.83/1.48  fof(f33,plain,(
% 7.83/1.48    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f32,plain,(
% 7.83/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f31,plain,(
% 7.83/1.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f34,plain,(
% 7.83/1.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 7.83/1.48  
% 7.83/1.48  fof(f63,plain,(
% 7.83/1.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f34])).
% 7.83/1.48  
% 7.83/1.48  fof(f92,plain,(
% 7.83/1.48    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 7.83/1.48    inference(equality_resolution,[],[f63])).
% 7.83/1.48  
% 7.83/1.48  fof(f11,conjecture,(
% 7.83/1.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f12,negated_conjecture,(
% 7.83/1.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.83/1.48    inference(negated_conjecture,[],[f11])).
% 7.83/1.48  
% 7.83/1.48  fof(f19,plain,(
% 7.83/1.48    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.83/1.48    inference(ennf_transformation,[],[f12])).
% 7.83/1.48  
% 7.83/1.48  fof(f45,plain,(
% 7.83/1.48    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.83/1.48    inference(nnf_transformation,[],[f19])).
% 7.83/1.48  
% 7.83/1.48  fof(f46,plain,(
% 7.83/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.83/1.48    inference(flattening,[],[f45])).
% 7.83/1.48  
% 7.83/1.48  fof(f47,plain,(
% 7.83/1.48    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f48,plain,(
% 7.83/1.48    (~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11)),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f46,f47])).
% 7.83/1.48  
% 7.83/1.48  fof(f76,plain,(
% 7.83/1.48    v1_relat_1(sK11)),
% 7.83/1.48    inference(cnf_transformation,[],[f48])).
% 7.83/1.48  
% 7.83/1.48  fof(f55,plain,(
% 7.83/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f26])).
% 7.83/1.48  
% 7.83/1.48  fof(f86,plain,(
% 7.83/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 7.83/1.48    inference(definition_unfolding,[],[f55,f60])).
% 7.83/1.48  
% 7.83/1.48  fof(f78,plain,(
% 7.83/1.48    ~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)),
% 7.83/1.48    inference(cnf_transformation,[],[f48])).
% 7.83/1.48  
% 7.83/1.48  fof(f3,axiom,(
% 7.83/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f15,plain,(
% 7.83/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.83/1.48    inference(ennf_transformation,[],[f3])).
% 7.83/1.48  
% 7.83/1.48  fof(f27,plain,(
% 7.83/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f28,plain,(
% 7.83/1.48    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).
% 7.83/1.48  
% 7.83/1.48  fof(f57,plain,(
% 7.83/1.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.83/1.48    inference(cnf_transformation,[],[f28])).
% 7.83/1.48  
% 7.83/1.48  fof(f9,axiom,(
% 7.83/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f17,plain,(
% 7.83/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.83/1.48    inference(ennf_transformation,[],[f9])).
% 7.83/1.48  
% 7.83/1.48  fof(f41,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.83/1.48    inference(nnf_transformation,[],[f17])).
% 7.83/1.48  
% 7.83/1.48  fof(f42,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.83/1.48    inference(rectify,[],[f41])).
% 7.83/1.48  
% 7.83/1.48  fof(f43,plain,(
% 7.83/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f44,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).
% 7.83/1.48  
% 7.83/1.48  fof(f73,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f44])).
% 7.83/1.48  
% 7.83/1.48  fof(f77,plain,(
% 7.83/1.48    r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)),
% 7.83/1.48    inference(cnf_transformation,[],[f48])).
% 7.83/1.48  
% 7.83/1.48  fof(f10,axiom,(
% 7.83/1.48    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f18,plain,(
% 7.83/1.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.83/1.48    inference(ennf_transformation,[],[f10])).
% 7.83/1.48  
% 7.83/1.48  fof(f75,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f18])).
% 7.83/1.48  
% 7.83/1.48  fof(f88,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.83/1.48    inference(definition_unfolding,[],[f75,f60])).
% 7.83/1.48  
% 7.83/1.48  fof(f8,axiom,(
% 7.83/1.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f35,plain,(
% 7.83/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.83/1.48    inference(nnf_transformation,[],[f8])).
% 7.83/1.48  
% 7.83/1.48  fof(f36,plain,(
% 7.83/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.83/1.48    inference(rectify,[],[f35])).
% 7.83/1.48  
% 7.83/1.48  fof(f39,plain,(
% 7.83/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f38,plain,(
% 7.83/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f37,plain,(
% 7.83/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f40,plain,(
% 7.83/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).
% 7.83/1.48  
% 7.83/1.48  fof(f67,plain,(
% 7.83/1.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.83/1.48    inference(cnf_transformation,[],[f40])).
% 7.83/1.48  
% 7.83/1.48  fof(f96,plain,(
% 7.83/1.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.83/1.48    inference(equality_resolution,[],[f67])).
% 7.83/1.48  
% 7.83/1.48  fof(f49,plain,(
% 7.83/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.83/1.48    inference(cnf_transformation,[],[f24])).
% 7.83/1.48  
% 7.83/1.48  fof(f84,plain,(
% 7.83/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 7.83/1.48    inference(definition_unfolding,[],[f49,f60])).
% 7.83/1.48  
% 7.83/1.48  fof(f91,plain,(
% 7.83/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.83/1.48    inference(equality_resolution,[],[f84])).
% 7.83/1.48  
% 7.83/1.48  cnf(c_6,plain,
% 7.83/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.83/1.48      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_10,plain,
% 7.83/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.83/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_388,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 7.83/1.48      | X3 != X1
% 7.83/1.48      | k1_xboole_0 != X2 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_389,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_388]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_22875,plain,
% 7.83/1.48      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),k1_xboole_0))) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_389]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_3,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,X1)
% 7.83/1.48      | ~ r2_hidden(X0,X2)
% 7.83/1.48      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7198,plain,
% 7.83/1.48      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 7.83/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
% 7.83/1.48      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),X0))) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7200,plain,
% 7.83/1.48      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
% 7.83/1.48      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_setfam_1(k2_tarski(k10_relat_1(sK11,k2_relat_1(sK11)),k1_xboole_0)))
% 7.83/1.48      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_7198]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_14,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,X1)
% 7.83/1.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.83/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.83/1.48      | ~ v1_relat_1(X3) ),
% 7.83/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_28,negated_conjecture,
% 7.83/1.48      ( v1_relat_1(sK11) ),
% 7.83/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_494,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,X1)
% 7.83/1.48      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.83/1.48      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.83/1.48      | sK11 != X3 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_495,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,X1)
% 7.83/1.48      | r2_hidden(X2,k10_relat_1(sK11,X1))
% 7.83/1.48      | ~ r2_hidden(k4_tarski(X2,X0),sK11) ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_494]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4094,plain,
% 7.83/1.48      ( r2_hidden(X0,k10_relat_1(sK11,k2_relat_1(sK11)))
% 7.83/1.48      | ~ r2_hidden(k4_tarski(X0,sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.83/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_495]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5680,plain,
% 7.83/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k2_relat_1(sK11)))
% 7.83/1.48      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.83/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_4094]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7,plain,
% 7.83/1.48      ( r1_xboole_0(X0,X1)
% 7.83/1.48      | r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_26,negated_conjecture,
% 7.83/1.48      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.83/1.48      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 7.83/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_223,plain,
% 7.83/1.48      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.83/1.48      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 7.83/1.48      inference(prop_impl,[status(thm)],[c_26]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_397,plain,
% 7.83/1.48      ( r2_hidden(sK1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
% 7.83/1.48      | k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.83/1.48      | k2_relat_1(sK11) != X0
% 7.83/1.48      | sK10 != X1 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_7,c_223]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_398,plain,
% 7.83/1.48      ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))
% 7.83/1.48      | k10_relat_1(sK11,sK10) != k1_xboole_0 ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_397]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1210,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.83/1.48      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_399,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 7.83/1.48      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_8,plain,
% 7.83/1.48      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.83/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1217,plain,
% 7.83/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_22,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.83/1.48      | r2_hidden(sK9(X0,X2,X1),X2)
% 7.83/1.48      | ~ v1_relat_1(X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_533,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 7.83/1.48      | r2_hidden(sK9(X0,X2,X1),X2)
% 7.83/1.48      | sK11 != X1 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_534,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k10_relat_1(sK11,X1))
% 7.83/1.48      | r2_hidden(sK9(X0,X1,sK11),X1) ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_533]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1202,plain,
% 7.83/1.48      ( r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 7.83/1.48      | r2_hidden(sK9(X0,X1,sK11),X1) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_27,negated_conjecture,
% 7.83/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.83/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.83/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_225,plain,
% 7.83/1.48      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 7.83/1.48      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 7.83/1.48      inference(prop_impl,[status(thm)],[c_27]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_407,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 7.83/1.48      | k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.83/1.48      | k2_relat_1(sK11) != X1
% 7.83/1.48      | sK10 != X2 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_6,c_225]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_408,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))
% 7.83/1.48      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_407]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1209,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.83/1.48      | r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2669,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.83/1.48      | r2_hidden(X0,k10_relat_1(sK11,k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10)))) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_1202,c_1209]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_25,plain,
% 7.83/1.48      ( ~ v1_relat_1(X0)
% 7.83/1.48      | k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_440,plain,
% 7.83/1.48      ( k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 7.83/1.48      | sK11 != X0 ),
% 7.83/1.48      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_441,plain,
% 7.83/1.48      ( k10_relat_1(sK11,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X0))) = k10_relat_1(sK11,X0) ),
% 7.83/1.48      inference(unflattening,[status(thm)],[c_440]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2673,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 7.83/1.48      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
% 7.83/1.48      inference(demodulation,[status(thm)],[c_2669,c_441]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_3164,plain,
% 7.83/1.48      ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_1217,c_2673]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_3679,plain,
% 7.83/1.48      ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) = iProver_top ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_1210,c_399,c_3164]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_20,plain,
% 7.83/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.83/1.48      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1213,plain,
% 7.83/1.48      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.83/1.48      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1205,plain,
% 7.83/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.83/1.48      | r2_hidden(X2,k10_relat_1(sK11,X1)) = iProver_top
% 7.83/1.48      | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2958,plain,
% 7.83/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.83/1.48      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 7.83/1.48      | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_1213,c_1205]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4804,plain,
% 7.83/1.48      ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 7.83/1.48      | r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X1))) != iProver_top
% 7.83/1.48      | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_441,c_2958]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5,plain,
% 7.83/1.48      ( r2_hidden(X0,X1)
% 7.83/1.48      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1218,plain,
% 7.83/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.83/1.48      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4835,plain,
% 7.83/1.48      ( r2_hidden(X0,k1_setfam_1(k2_tarski(k2_relat_1(sK11),X1))) != iProver_top
% 7.83/1.48      | r2_hidden(sK8(sK11,X0),k10_relat_1(sK11,X1)) = iProver_top ),
% 7.83/1.48      inference(forward_subsumption_resolution,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_4804,c_1218]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4843,plain,
% 7.83/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,sK10)) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_3679,c_4835]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4893,plain,
% 7.83/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) = iProver_top ),
% 7.83/1.48      inference(light_normalisation,[status(thm)],[c_4843,c_3164]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4936,plain,
% 7.83/1.48      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 7.83/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4893]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_4112,plain,
% 7.83/1.48      ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 7.83/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1648,plain,
% 7.83/1.48      ( r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11))
% 7.83/1.48      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k1_setfam_1(k2_tarski(k2_relat_1(sK11),sK10))) ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(contradiction,plain,
% 7.83/1.48      ( $false ),
% 7.83/1.48      inference(minisat,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_22875,c_7200,c_5680,c_4936,c_4112,c_3164,c_1648,c_398]) ).
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  ------                               Statistics
% 7.83/1.48  
% 7.83/1.48  ------ Selected
% 7.83/1.48  
% 7.83/1.48  total_time:                             0.928
% 7.83/1.48  
%------------------------------------------------------------------------------
