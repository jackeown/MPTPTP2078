%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:31 EST 2020

% Result     : Theorem 55.46s
% Output     : CNFRefutation 55.46s
% Verified   : 
% Statistics : Number of formulae       :  207 (2216 expanded)
%              Number of clauses        :  132 ( 553 expanded)
%              Number of leaves         :   19 ( 398 expanded)
%              Depth                    :   29
%              Number of atoms          :  881 (13718 expanded)
%              Number of equality atoms :  219 (1034 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
          | sK1(X0,X1,X2) = X1
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
            & sK1(X0,X1,X2) != X1 )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                | sK1(X0,X1,X2) = X1
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                  & sK1(X0,X1,X2) != X1 )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
        | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) )
      & ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
        | r2_hidden(k4_tarski(sK10,sK11),sK12) )
      & r2_hidden(sK11,k3_relat_1(sK12))
      & r2_hidden(sK10,k3_relat_1(sK12))
      & v2_wellord1(sK12)
      & v1_relat_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
      | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) )
    & ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
      | r2_hidden(k4_tarski(sK10,sK11),sK12) )
    & r2_hidden(sK11,k3_relat_1(sK12))
    & r2_hidden(sK10,k3_relat_1(sK12))
    & v2_wellord1(sK12)
    & v1_relat_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f49,f50])).

fof(f84,plain,(
    v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0)
            & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f38])).

fof(f70,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    v2_wellord1(sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK9(X0),sK8(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
        & sK8(X0) != sK9(X0)
        & r2_hidden(sK9(X0),k3_relat_1(X0))
        & r2_hidden(sK8(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK9(X0),sK8(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
            & sK8(X0) != sK9(X0)
            & r2_hidden(sK9(X0),k3_relat_1(X0))
            & r2_hidden(sK8(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f46])).

fof(f78,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f51])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f93,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f87,plain,(
    r2_hidden(sK11,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f67,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK6(X0) != sK7(X0)
        & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK6(X0) != sK7(X0)
            & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).

fof(f74,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,
    ( ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1511,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_105192,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(sK12,X3))
    | X2 != X0
    | k1_wellord1(sK12,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_106665,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK12,X1))
    | r2_hidden(X2,k1_wellord1(sK12,X1))
    | X2 != X0
    | k1_wellord1(sK12,X1) != k1_wellord1(sK12,X1) ),
    inference(instantiation,[status(thm)],[c_105192])).

cnf(c_108909,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,sK10))
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
    | X0 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | k1_wellord1(sK12,sK10) != k1_wellord1(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_106665])).

cnf(c_118839,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
    | r2_hidden(sK11,k1_wellord1(sK12,sK10))
    | k1_wellord1(sK12,sK10) != k1_wellord1(sK12,sK10)
    | sK11 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_108909])).

cnf(c_1508,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_50952,plain,
    ( sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_1985,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(sK12,X3))
    | X2 != X0
    | k1_wellord1(sK12,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_6777,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X1))
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
    | X0 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | k1_wellord1(sK12,X1) != k1_wellord1(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_15182,plain,
    ( r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,X0))
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
    | k1_wellord1(sK12,X0) != k1_wellord1(sK12,sK10)
    | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_6777])).

cnf(c_38768,plain,
    ( r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11))
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
    | k1_wellord1(sK12,sK11) != k1_wellord1(sK12,sK10)
    | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_15182])).

cnf(c_38769,plain,
    ( k1_wellord1(sK12,sK11) != k1_wellord1(sK12,sK10)
    | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38768])).

cnf(c_1512,plain,
    ( X0 != X1
    | X2 != X3
    | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
    theory(equality)).

cnf(c_14508,plain,
    ( k1_wellord1(sK12,sK11) = k1_wellord1(sK12,X0)
    | sK11 != X0
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_38514,plain,
    ( k1_wellord1(sK12,sK11) = k1_wellord1(sK12,sK10)
    | sK11 != sK10
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_14508])).

cnf(c_30784,plain,
    ( k1_wellord1(sK12,sK10) = k1_wellord1(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1193,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_37])).

cnf(c_1194,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1193])).

cnf(c_15169,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),X0),sK12)
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,X0))
    | X0 = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_29288,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK11),sK12)
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11))
    | sK11 = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(instantiation,[status(thm)],[c_15169])).

cnf(c_21,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1223,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_1224,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ v8_relat_2(sK12) ),
    inference(unflattening,[status(thm)],[c_1223])).

cnf(c_13,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,negated_conjecture,
    ( v2_wellord1(sK12) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_501,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_502,plain,
    ( v8_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_97,plain,
    ( v8_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_504,plain,
    ( v8_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_37,c_36,c_97])).

cnf(c_840,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_504])).

cnf(c_841,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_843,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_37])).

cnf(c_844,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12) ),
    inference(renaming,[status(thm)],[c_843])).

cnf(c_1226,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1224,c_37,c_841])).

cnf(c_1227,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12) ),
    inference(renaming,[status(thm)],[c_1226])).

cnf(c_3956,plain,
    ( r2_hidden(k4_tarski(X0,sK11),sK12)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK12)
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_13119,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK11),sK12)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK10),sK12)
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(instantiation,[status(thm)],[c_3956])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12)
    | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1912,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1137,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_1138,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ v6_relat_2(sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1137])).

cnf(c_11,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_523,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_524,plain,
    ( v6_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_103,plain,
    ( v6_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_526,plain,
    ( v6_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_37,c_36,c_103])).

cnf(c_1000,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_526])).

cnf(c_1001,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ v1_relat_1(sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1000])).

cnf(c_1140,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK12)
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | ~ r2_hidden(X0,k3_relat_1(sK12))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_37,c_1001])).

cnf(c_1141,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1140])).

cnf(c_1906,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_1900,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_3116,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1900])).

cnf(c_7763,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_1900])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1914,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8966,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r1_tarski(k1_wellord1(sK12,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7763,c_1914])).

cnf(c_10565,plain,
    ( sK10 = X0
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_8966])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( r2_hidden(sK10,k3_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10571,plain,
    ( r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | sK10 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10565,c_40])).

cnf(c_10572,plain,
    ( sK10 = X0
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10571])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1174,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_37])).

cnf(c_1175,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK12,X0)) ),
    inference(unflattening,[status(thm)],[c_1174])).

cnf(c_1902,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_10589,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK11,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10572,c_1902])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK11,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( r2_hidden(sK11,k3_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1523,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1160,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1161,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ v1_relat_2(sK12) ),
    inference(unflattening,[status(thm)],[c_1160])).

cnf(c_14,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_490,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_491,plain,
    ( v1_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_94,plain,
    ( v1_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_493,plain,
    ( v1_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_37,c_36,c_94])).

cnf(c_578,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_493])).

cnf(c_579,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_583,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_37])).

cnf(c_584,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12) ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_1163,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_37,c_579])).

cnf(c_1164,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12) ),
    inference(renaming,[status(thm)],[c_1163])).

cnf(c_1969,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),sK12)
    | ~ r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1970,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),sK12) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1969])).

cnf(c_1951,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK10,sK11),sK12)
    | k4_tarski(sK10,sK11) != X0
    | sK12 != X1 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_2015,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ r2_hidden(k4_tarski(sK10,sK10),sK12)
    | k4_tarski(sK10,sK11) != k4_tarski(sK10,sK10)
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_2016,plain,
    ( k4_tarski(sK10,sK11) != k4_tarski(sK10,sK10)
    | sK12 != sK12
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK10),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_1514,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_2072,plain,
    ( k4_tarski(sK10,sK11) = k4_tarski(sK10,sK10)
    | sK11 != sK10
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_25,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1206,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | X1 = X0
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_1207,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ v4_relat_2(sK12)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_12,plain,
    ( v4_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_512,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_513,plain,
    ( v4_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_100,plain,
    ( v4_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_515,plain,
    ( v4_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_37,c_36,c_100])).

cnf(c_744,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_515])).

cnf(c_745,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ v1_relat_1(sK12)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_1209,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_37,c_745])).

cnf(c_1210,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1209])).

cnf(c_2302,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK10),sK12)
    | ~ r2_hidden(k4_tarski(sK10,X0),sK12)
    | X0 = sK10 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_2918,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK10),sK12)
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_10742,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10589,c_35,c_40,c_41,c_1523,c_1969,c_1970,c_2016,c_2072,c_2918])).

cnf(c_10747,plain,
    ( sK11 = sK10
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10742,c_1900])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1183,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_37])).

cnf(c_1184,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK12,X1))
    | r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(unflattening,[status(thm)],[c_1183])).

cnf(c_1901,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_10911,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_10747,c_1901])).

cnf(c_10917,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10911,c_35,c_40,c_1523,c_1969,c_1970,c_2016,c_2072,c_2918])).

cnf(c_10919,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10917])).

cnf(c_6810,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK10),sK12)
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_4691,plain,
    ( ~ r2_hidden(k4_tarski(sK11,sK10),sK12)
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | sK11 = sK10 ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_2816,plain,
    ( r2_hidden(k4_tarski(sK11,X0),sK12)
    | ~ r2_hidden(sK11,k1_wellord1(sK12,X0)) ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_4690,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK12)
    | ~ r2_hidden(sK11,k1_wellord1(sK12,sK10)) ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_291,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_643,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_wellord1(sK12,sK11) != X1
    | k1_wellord1(sK12,sK10) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_291])).

cnf(c_644,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_645,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_633,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | r2_hidden(sK0(X0,X1),X0)
    | k1_wellord1(sK12,sK11) != X1
    | k1_wellord1(sK12,sK10) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_291])).

cnf(c_634,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_635,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118839,c_50952,c_38769,c_38514,c_30784,c_29288,c_13119,c_10919,c_10917,c_6810,c_4691,c_4690,c_1523,c_645,c_644,c_635,c_634])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.46/7.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.46/7.50  
% 55.46/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.46/7.50  
% 55.46/7.50  ------  iProver source info
% 55.46/7.50  
% 55.46/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.46/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.46/7.50  git: non_committed_changes: false
% 55.46/7.50  git: last_make_outside_of_git: false
% 55.46/7.50  
% 55.46/7.50  ------ 
% 55.46/7.50  
% 55.46/7.50  ------ Input Options
% 55.46/7.50  
% 55.46/7.50  --out_options                           all
% 55.46/7.50  --tptp_safe_out                         true
% 55.46/7.50  --problem_path                          ""
% 55.46/7.50  --include_path                          ""
% 55.46/7.50  --clausifier                            res/vclausify_rel
% 55.46/7.50  --clausifier_options                    ""
% 55.46/7.50  --stdin                                 false
% 55.46/7.50  --stats_out                             all
% 55.46/7.50  
% 55.46/7.50  ------ General Options
% 55.46/7.50  
% 55.46/7.50  --fof                                   false
% 55.46/7.50  --time_out_real                         305.
% 55.46/7.50  --time_out_virtual                      -1.
% 55.46/7.50  --symbol_type_check                     false
% 55.46/7.50  --clausify_out                          false
% 55.46/7.50  --sig_cnt_out                           false
% 55.46/7.50  --trig_cnt_out                          false
% 55.46/7.50  --trig_cnt_out_tolerance                1.
% 55.46/7.50  --trig_cnt_out_sk_spl                   false
% 55.46/7.50  --abstr_cl_out                          false
% 55.46/7.50  
% 55.46/7.50  ------ Global Options
% 55.46/7.50  
% 55.46/7.50  --schedule                              default
% 55.46/7.50  --add_important_lit                     false
% 55.46/7.50  --prop_solver_per_cl                    1000
% 55.46/7.50  --min_unsat_core                        false
% 55.46/7.50  --soft_assumptions                      false
% 55.46/7.50  --soft_lemma_size                       3
% 55.46/7.50  --prop_impl_unit_size                   0
% 55.46/7.50  --prop_impl_unit                        []
% 55.46/7.50  --share_sel_clauses                     true
% 55.46/7.50  --reset_solvers                         false
% 55.46/7.50  --bc_imp_inh                            [conj_cone]
% 55.46/7.50  --conj_cone_tolerance                   3.
% 55.46/7.50  --extra_neg_conj                        none
% 55.46/7.50  --large_theory_mode                     true
% 55.46/7.50  --prolific_symb_bound                   200
% 55.46/7.50  --lt_threshold                          2000
% 55.46/7.50  --clause_weak_htbl                      true
% 55.46/7.50  --gc_record_bc_elim                     false
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing Options
% 55.46/7.50  
% 55.46/7.50  --preprocessing_flag                    true
% 55.46/7.50  --time_out_prep_mult                    0.1
% 55.46/7.50  --splitting_mode                        input
% 55.46/7.50  --splitting_grd                         true
% 55.46/7.50  --splitting_cvd                         false
% 55.46/7.50  --splitting_cvd_svl                     false
% 55.46/7.50  --splitting_nvd                         32
% 55.46/7.50  --sub_typing                            true
% 55.46/7.50  --prep_gs_sim                           true
% 55.46/7.50  --prep_unflatten                        true
% 55.46/7.50  --prep_res_sim                          true
% 55.46/7.50  --prep_upred                            true
% 55.46/7.50  --prep_sem_filter                       exhaustive
% 55.46/7.50  --prep_sem_filter_out                   false
% 55.46/7.50  --pred_elim                             true
% 55.46/7.50  --res_sim_input                         true
% 55.46/7.50  --eq_ax_congr_red                       true
% 55.46/7.50  --pure_diseq_elim                       true
% 55.46/7.50  --brand_transform                       false
% 55.46/7.50  --non_eq_to_eq                          false
% 55.46/7.50  --prep_def_merge                        true
% 55.46/7.50  --prep_def_merge_prop_impl              false
% 55.46/7.50  --prep_def_merge_mbd                    true
% 55.46/7.50  --prep_def_merge_tr_red                 false
% 55.46/7.50  --prep_def_merge_tr_cl                  false
% 55.46/7.50  --smt_preprocessing                     true
% 55.46/7.50  --smt_ac_axioms                         fast
% 55.46/7.50  --preprocessed_out                      false
% 55.46/7.50  --preprocessed_stats                    false
% 55.46/7.50  
% 55.46/7.50  ------ Abstraction refinement Options
% 55.46/7.50  
% 55.46/7.50  --abstr_ref                             []
% 55.46/7.50  --abstr_ref_prep                        false
% 55.46/7.50  --abstr_ref_until_sat                   false
% 55.46/7.50  --abstr_ref_sig_restrict                funpre
% 55.46/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.46/7.50  --abstr_ref_under                       []
% 55.46/7.50  
% 55.46/7.50  ------ SAT Options
% 55.46/7.50  
% 55.46/7.50  --sat_mode                              false
% 55.46/7.50  --sat_fm_restart_options                ""
% 55.46/7.50  --sat_gr_def                            false
% 55.46/7.50  --sat_epr_types                         true
% 55.46/7.50  --sat_non_cyclic_types                  false
% 55.46/7.50  --sat_finite_models                     false
% 55.46/7.50  --sat_fm_lemmas                         false
% 55.46/7.50  --sat_fm_prep                           false
% 55.46/7.50  --sat_fm_uc_incr                        true
% 55.46/7.50  --sat_out_model                         small
% 55.46/7.50  --sat_out_clauses                       false
% 55.46/7.50  
% 55.46/7.50  ------ QBF Options
% 55.46/7.50  
% 55.46/7.50  --qbf_mode                              false
% 55.46/7.50  --qbf_elim_univ                         false
% 55.46/7.50  --qbf_dom_inst                          none
% 55.46/7.50  --qbf_dom_pre_inst                      false
% 55.46/7.50  --qbf_sk_in                             false
% 55.46/7.50  --qbf_pred_elim                         true
% 55.46/7.50  --qbf_split                             512
% 55.46/7.50  
% 55.46/7.50  ------ BMC1 Options
% 55.46/7.50  
% 55.46/7.50  --bmc1_incremental                      false
% 55.46/7.50  --bmc1_axioms                           reachable_all
% 55.46/7.50  --bmc1_min_bound                        0
% 55.46/7.50  --bmc1_max_bound                        -1
% 55.46/7.50  --bmc1_max_bound_default                -1
% 55.46/7.50  --bmc1_symbol_reachability              true
% 55.46/7.50  --bmc1_property_lemmas                  false
% 55.46/7.50  --bmc1_k_induction                      false
% 55.46/7.50  --bmc1_non_equiv_states                 false
% 55.46/7.50  --bmc1_deadlock                         false
% 55.46/7.50  --bmc1_ucm                              false
% 55.46/7.50  --bmc1_add_unsat_core                   none
% 55.46/7.50  --bmc1_unsat_core_children              false
% 55.46/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.46/7.50  --bmc1_out_stat                         full
% 55.46/7.50  --bmc1_ground_init                      false
% 55.46/7.50  --bmc1_pre_inst_next_state              false
% 55.46/7.50  --bmc1_pre_inst_state                   false
% 55.46/7.50  --bmc1_pre_inst_reach_state             false
% 55.46/7.50  --bmc1_out_unsat_core                   false
% 55.46/7.50  --bmc1_aig_witness_out                  false
% 55.46/7.50  --bmc1_verbose                          false
% 55.46/7.50  --bmc1_dump_clauses_tptp                false
% 55.46/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.46/7.50  --bmc1_dump_file                        -
% 55.46/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.46/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.46/7.50  --bmc1_ucm_extend_mode                  1
% 55.46/7.50  --bmc1_ucm_init_mode                    2
% 55.46/7.50  --bmc1_ucm_cone_mode                    none
% 55.46/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.46/7.50  --bmc1_ucm_relax_model                  4
% 55.46/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.46/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.46/7.50  --bmc1_ucm_layered_model                none
% 55.46/7.50  --bmc1_ucm_max_lemma_size               10
% 55.46/7.50  
% 55.46/7.50  ------ AIG Options
% 55.46/7.50  
% 55.46/7.50  --aig_mode                              false
% 55.46/7.50  
% 55.46/7.50  ------ Instantiation Options
% 55.46/7.50  
% 55.46/7.50  --instantiation_flag                    true
% 55.46/7.50  --inst_sos_flag                         true
% 55.46/7.50  --inst_sos_phase                        true
% 55.46/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.46/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.46/7.50  --inst_lit_sel_side                     num_symb
% 55.46/7.50  --inst_solver_per_active                1400
% 55.46/7.50  --inst_solver_calls_frac                1.
% 55.46/7.50  --inst_passive_queue_type               priority_queues
% 55.46/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.46/7.50  --inst_passive_queues_freq              [25;2]
% 55.46/7.50  --inst_dismatching                      true
% 55.46/7.50  --inst_eager_unprocessed_to_passive     true
% 55.46/7.50  --inst_prop_sim_given                   true
% 55.46/7.50  --inst_prop_sim_new                     false
% 55.46/7.50  --inst_subs_new                         false
% 55.46/7.50  --inst_eq_res_simp                      false
% 55.46/7.50  --inst_subs_given                       false
% 55.46/7.50  --inst_orphan_elimination               true
% 55.46/7.50  --inst_learning_loop_flag               true
% 55.46/7.50  --inst_learning_start                   3000
% 55.46/7.50  --inst_learning_factor                  2
% 55.46/7.50  --inst_start_prop_sim_after_learn       3
% 55.46/7.50  --inst_sel_renew                        solver
% 55.46/7.50  --inst_lit_activity_flag                true
% 55.46/7.50  --inst_restr_to_given                   false
% 55.46/7.50  --inst_activity_threshold               500
% 55.46/7.50  --inst_out_proof                        true
% 55.46/7.50  
% 55.46/7.50  ------ Resolution Options
% 55.46/7.50  
% 55.46/7.50  --resolution_flag                       true
% 55.46/7.50  --res_lit_sel                           adaptive
% 55.46/7.50  --res_lit_sel_side                      none
% 55.46/7.50  --res_ordering                          kbo
% 55.46/7.50  --res_to_prop_solver                    active
% 55.46/7.50  --res_prop_simpl_new                    false
% 55.46/7.50  --res_prop_simpl_given                  true
% 55.46/7.50  --res_passive_queue_type                priority_queues
% 55.46/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.46/7.50  --res_passive_queues_freq               [15;5]
% 55.46/7.50  --res_forward_subs                      full
% 55.46/7.50  --res_backward_subs                     full
% 55.46/7.50  --res_forward_subs_resolution           true
% 55.46/7.50  --res_backward_subs_resolution          true
% 55.46/7.50  --res_orphan_elimination                true
% 55.46/7.50  --res_time_limit                        2.
% 55.46/7.50  --res_out_proof                         true
% 55.46/7.50  
% 55.46/7.50  ------ Superposition Options
% 55.46/7.50  
% 55.46/7.50  --superposition_flag                    true
% 55.46/7.50  --sup_passive_queue_type                priority_queues
% 55.46/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.46/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.46/7.50  --demod_completeness_check              fast
% 55.46/7.50  --demod_use_ground                      true
% 55.46/7.50  --sup_to_prop_solver                    passive
% 55.46/7.50  --sup_prop_simpl_new                    true
% 55.46/7.50  --sup_prop_simpl_given                  true
% 55.46/7.50  --sup_fun_splitting                     true
% 55.46/7.50  --sup_smt_interval                      50000
% 55.46/7.50  
% 55.46/7.50  ------ Superposition Simplification Setup
% 55.46/7.50  
% 55.46/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.46/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.46/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.46/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.46/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.46/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.46/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.46/7.50  --sup_immed_triv                        [TrivRules]
% 55.46/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_immed_bw_main                     []
% 55.46/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.46/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.46/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_input_bw                          []
% 55.46/7.50  
% 55.46/7.50  ------ Combination Options
% 55.46/7.50  
% 55.46/7.50  --comb_res_mult                         3
% 55.46/7.50  --comb_sup_mult                         2
% 55.46/7.50  --comb_inst_mult                        10
% 55.46/7.50  
% 55.46/7.50  ------ Debug Options
% 55.46/7.50  
% 55.46/7.50  --dbg_backtrace                         false
% 55.46/7.50  --dbg_dump_prop_clauses                 false
% 55.46/7.50  --dbg_dump_prop_clauses_file            -
% 55.46/7.50  --dbg_out_stat                          false
% 55.46/7.50  ------ Parsing...
% 55.46/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.46/7.50  ------ Proving...
% 55.46/7.50  ------ Problem Properties 
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  clauses                                 17
% 55.46/7.50  conjectures                             4
% 55.46/7.50  EPR                                     1
% 55.46/7.50  Horn                                    10
% 55.46/7.50  unary                                   3
% 55.46/7.50  binary                                  6
% 55.46/7.50  lits                                    42
% 55.46/7.50  lits eq                                 8
% 55.46/7.50  fd_pure                                 0
% 55.46/7.50  fd_pseudo                               0
% 55.46/7.50  fd_cond                                 0
% 55.46/7.50  fd_pseudo_cond                          5
% 55.46/7.50  AC symbols                              0
% 55.46/7.50  
% 55.46/7.50  ------ Schedule dynamic 5 is on 
% 55.46/7.50  
% 55.46/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  ------ 
% 55.46/7.50  Current options:
% 55.46/7.50  ------ 
% 55.46/7.50  
% 55.46/7.50  ------ Input Options
% 55.46/7.50  
% 55.46/7.50  --out_options                           all
% 55.46/7.50  --tptp_safe_out                         true
% 55.46/7.50  --problem_path                          ""
% 55.46/7.50  --include_path                          ""
% 55.46/7.50  --clausifier                            res/vclausify_rel
% 55.46/7.50  --clausifier_options                    ""
% 55.46/7.50  --stdin                                 false
% 55.46/7.50  --stats_out                             all
% 55.46/7.50  
% 55.46/7.50  ------ General Options
% 55.46/7.50  
% 55.46/7.50  --fof                                   false
% 55.46/7.50  --time_out_real                         305.
% 55.46/7.50  --time_out_virtual                      -1.
% 55.46/7.50  --symbol_type_check                     false
% 55.46/7.50  --clausify_out                          false
% 55.46/7.50  --sig_cnt_out                           false
% 55.46/7.50  --trig_cnt_out                          false
% 55.46/7.50  --trig_cnt_out_tolerance                1.
% 55.46/7.50  --trig_cnt_out_sk_spl                   false
% 55.46/7.50  --abstr_cl_out                          false
% 55.46/7.50  
% 55.46/7.50  ------ Global Options
% 55.46/7.50  
% 55.46/7.50  --schedule                              default
% 55.46/7.50  --add_important_lit                     false
% 55.46/7.50  --prop_solver_per_cl                    1000
% 55.46/7.50  --min_unsat_core                        false
% 55.46/7.50  --soft_assumptions                      false
% 55.46/7.50  --soft_lemma_size                       3
% 55.46/7.50  --prop_impl_unit_size                   0
% 55.46/7.50  --prop_impl_unit                        []
% 55.46/7.50  --share_sel_clauses                     true
% 55.46/7.50  --reset_solvers                         false
% 55.46/7.50  --bc_imp_inh                            [conj_cone]
% 55.46/7.50  --conj_cone_tolerance                   3.
% 55.46/7.50  --extra_neg_conj                        none
% 55.46/7.50  --large_theory_mode                     true
% 55.46/7.50  --prolific_symb_bound                   200
% 55.46/7.50  --lt_threshold                          2000
% 55.46/7.50  --clause_weak_htbl                      true
% 55.46/7.50  --gc_record_bc_elim                     false
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing Options
% 55.46/7.50  
% 55.46/7.50  --preprocessing_flag                    true
% 55.46/7.50  --time_out_prep_mult                    0.1
% 55.46/7.50  --splitting_mode                        input
% 55.46/7.50  --splitting_grd                         true
% 55.46/7.50  --splitting_cvd                         false
% 55.46/7.50  --splitting_cvd_svl                     false
% 55.46/7.50  --splitting_nvd                         32
% 55.46/7.50  --sub_typing                            true
% 55.46/7.50  --prep_gs_sim                           true
% 55.46/7.50  --prep_unflatten                        true
% 55.46/7.50  --prep_res_sim                          true
% 55.46/7.50  --prep_upred                            true
% 55.46/7.50  --prep_sem_filter                       exhaustive
% 55.46/7.50  --prep_sem_filter_out                   false
% 55.46/7.50  --pred_elim                             true
% 55.46/7.50  --res_sim_input                         true
% 55.46/7.50  --eq_ax_congr_red                       true
% 55.46/7.50  --pure_diseq_elim                       true
% 55.46/7.50  --brand_transform                       false
% 55.46/7.50  --non_eq_to_eq                          false
% 55.46/7.50  --prep_def_merge                        true
% 55.46/7.50  --prep_def_merge_prop_impl              false
% 55.46/7.50  --prep_def_merge_mbd                    true
% 55.46/7.50  --prep_def_merge_tr_red                 false
% 55.46/7.50  --prep_def_merge_tr_cl                  false
% 55.46/7.50  --smt_preprocessing                     true
% 55.46/7.50  --smt_ac_axioms                         fast
% 55.46/7.50  --preprocessed_out                      false
% 55.46/7.50  --preprocessed_stats                    false
% 55.46/7.50  
% 55.46/7.50  ------ Abstraction refinement Options
% 55.46/7.50  
% 55.46/7.50  --abstr_ref                             []
% 55.46/7.50  --abstr_ref_prep                        false
% 55.46/7.50  --abstr_ref_until_sat                   false
% 55.46/7.50  --abstr_ref_sig_restrict                funpre
% 55.46/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.46/7.50  --abstr_ref_under                       []
% 55.46/7.50  
% 55.46/7.50  ------ SAT Options
% 55.46/7.50  
% 55.46/7.50  --sat_mode                              false
% 55.46/7.50  --sat_fm_restart_options                ""
% 55.46/7.50  --sat_gr_def                            false
% 55.46/7.50  --sat_epr_types                         true
% 55.46/7.50  --sat_non_cyclic_types                  false
% 55.46/7.50  --sat_finite_models                     false
% 55.46/7.50  --sat_fm_lemmas                         false
% 55.46/7.50  --sat_fm_prep                           false
% 55.46/7.50  --sat_fm_uc_incr                        true
% 55.46/7.50  --sat_out_model                         small
% 55.46/7.50  --sat_out_clauses                       false
% 55.46/7.50  
% 55.46/7.50  ------ QBF Options
% 55.46/7.50  
% 55.46/7.50  --qbf_mode                              false
% 55.46/7.50  --qbf_elim_univ                         false
% 55.46/7.50  --qbf_dom_inst                          none
% 55.46/7.50  --qbf_dom_pre_inst                      false
% 55.46/7.50  --qbf_sk_in                             false
% 55.46/7.50  --qbf_pred_elim                         true
% 55.46/7.50  --qbf_split                             512
% 55.46/7.50  
% 55.46/7.50  ------ BMC1 Options
% 55.46/7.50  
% 55.46/7.50  --bmc1_incremental                      false
% 55.46/7.50  --bmc1_axioms                           reachable_all
% 55.46/7.50  --bmc1_min_bound                        0
% 55.46/7.50  --bmc1_max_bound                        -1
% 55.46/7.50  --bmc1_max_bound_default                -1
% 55.46/7.50  --bmc1_symbol_reachability              true
% 55.46/7.50  --bmc1_property_lemmas                  false
% 55.46/7.50  --bmc1_k_induction                      false
% 55.46/7.50  --bmc1_non_equiv_states                 false
% 55.46/7.50  --bmc1_deadlock                         false
% 55.46/7.50  --bmc1_ucm                              false
% 55.46/7.50  --bmc1_add_unsat_core                   none
% 55.46/7.50  --bmc1_unsat_core_children              false
% 55.46/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.46/7.50  --bmc1_out_stat                         full
% 55.46/7.50  --bmc1_ground_init                      false
% 55.46/7.50  --bmc1_pre_inst_next_state              false
% 55.46/7.50  --bmc1_pre_inst_state                   false
% 55.46/7.50  --bmc1_pre_inst_reach_state             false
% 55.46/7.50  --bmc1_out_unsat_core                   false
% 55.46/7.50  --bmc1_aig_witness_out                  false
% 55.46/7.50  --bmc1_verbose                          false
% 55.46/7.50  --bmc1_dump_clauses_tptp                false
% 55.46/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.46/7.50  --bmc1_dump_file                        -
% 55.46/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.46/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.46/7.50  --bmc1_ucm_extend_mode                  1
% 55.46/7.50  --bmc1_ucm_init_mode                    2
% 55.46/7.50  --bmc1_ucm_cone_mode                    none
% 55.46/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.46/7.50  --bmc1_ucm_relax_model                  4
% 55.46/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.46/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.46/7.50  --bmc1_ucm_layered_model                none
% 55.46/7.50  --bmc1_ucm_max_lemma_size               10
% 55.46/7.50  
% 55.46/7.50  ------ AIG Options
% 55.46/7.50  
% 55.46/7.50  --aig_mode                              false
% 55.46/7.50  
% 55.46/7.50  ------ Instantiation Options
% 55.46/7.50  
% 55.46/7.50  --instantiation_flag                    true
% 55.46/7.50  --inst_sos_flag                         true
% 55.46/7.50  --inst_sos_phase                        true
% 55.46/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.46/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.46/7.50  --inst_lit_sel_side                     none
% 55.46/7.50  --inst_solver_per_active                1400
% 55.46/7.50  --inst_solver_calls_frac                1.
% 55.46/7.50  --inst_passive_queue_type               priority_queues
% 55.46/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.46/7.50  --inst_passive_queues_freq              [25;2]
% 55.46/7.50  --inst_dismatching                      true
% 55.46/7.50  --inst_eager_unprocessed_to_passive     true
% 55.46/7.50  --inst_prop_sim_given                   true
% 55.46/7.50  --inst_prop_sim_new                     false
% 55.46/7.50  --inst_subs_new                         false
% 55.46/7.50  --inst_eq_res_simp                      false
% 55.46/7.50  --inst_subs_given                       false
% 55.46/7.50  --inst_orphan_elimination               true
% 55.46/7.50  --inst_learning_loop_flag               true
% 55.46/7.50  --inst_learning_start                   3000
% 55.46/7.50  --inst_learning_factor                  2
% 55.46/7.50  --inst_start_prop_sim_after_learn       3
% 55.46/7.50  --inst_sel_renew                        solver
% 55.46/7.50  --inst_lit_activity_flag                true
% 55.46/7.50  --inst_restr_to_given                   false
% 55.46/7.50  --inst_activity_threshold               500
% 55.46/7.50  --inst_out_proof                        true
% 55.46/7.50  
% 55.46/7.50  ------ Resolution Options
% 55.46/7.50  
% 55.46/7.50  --resolution_flag                       false
% 55.46/7.50  --res_lit_sel                           adaptive
% 55.46/7.50  --res_lit_sel_side                      none
% 55.46/7.50  --res_ordering                          kbo
% 55.46/7.50  --res_to_prop_solver                    active
% 55.46/7.50  --res_prop_simpl_new                    false
% 55.46/7.50  --res_prop_simpl_given                  true
% 55.46/7.50  --res_passive_queue_type                priority_queues
% 55.46/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.46/7.50  --res_passive_queues_freq               [15;5]
% 55.46/7.50  --res_forward_subs                      full
% 55.46/7.50  --res_backward_subs                     full
% 55.46/7.50  --res_forward_subs_resolution           true
% 55.46/7.50  --res_backward_subs_resolution          true
% 55.46/7.50  --res_orphan_elimination                true
% 55.46/7.50  --res_time_limit                        2.
% 55.46/7.50  --res_out_proof                         true
% 55.46/7.50  
% 55.46/7.50  ------ Superposition Options
% 55.46/7.50  
% 55.46/7.50  --superposition_flag                    true
% 55.46/7.50  --sup_passive_queue_type                priority_queues
% 55.46/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.46/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.46/7.50  --demod_completeness_check              fast
% 55.46/7.50  --demod_use_ground                      true
% 55.46/7.50  --sup_to_prop_solver                    passive
% 55.46/7.50  --sup_prop_simpl_new                    true
% 55.46/7.50  --sup_prop_simpl_given                  true
% 55.46/7.50  --sup_fun_splitting                     true
% 55.46/7.50  --sup_smt_interval                      50000
% 55.46/7.50  
% 55.46/7.50  ------ Superposition Simplification Setup
% 55.46/7.50  
% 55.46/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.46/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.46/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.46/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.46/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.46/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.46/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.46/7.50  --sup_immed_triv                        [TrivRules]
% 55.46/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_immed_bw_main                     []
% 55.46/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.46/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.46/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.46/7.50  --sup_input_bw                          []
% 55.46/7.50  
% 55.46/7.50  ------ Combination Options
% 55.46/7.50  
% 55.46/7.50  --comb_res_mult                         3
% 55.46/7.50  --comb_sup_mult                         2
% 55.46/7.50  --comb_inst_mult                        10
% 55.46/7.50  
% 55.46/7.50  ------ Debug Options
% 55.46/7.50  
% 55.46/7.50  --dbg_backtrace                         false
% 55.46/7.50  --dbg_dump_prop_clauses                 false
% 55.46/7.50  --dbg_dump_prop_clauses_file            -
% 55.46/7.50  --dbg_out_stat                          false
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  ------ Proving...
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  % SZS status Theorem for theBenchmark.p
% 55.46/7.50  
% 55.46/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.46/7.50  
% 55.46/7.50  fof(f2,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f11,plain,(
% 55.46/7.50    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f2])).
% 55.46/7.50  
% 55.46/7.50  fof(f25,plain,(
% 55.46/7.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f11])).
% 55.46/7.50  
% 55.46/7.50  fof(f26,plain,(
% 55.46/7.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(flattening,[],[f25])).
% 55.46/7.50  
% 55.46/7.50  fof(f27,plain,(
% 55.46/7.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(rectify,[],[f26])).
% 55.46/7.50  
% 55.46/7.50  fof(f28,plain,(
% 55.46/7.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f29,plain,(
% 55.46/7.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 55.46/7.50  
% 55.46/7.50  fof(f57,plain,(
% 55.46/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f29])).
% 55.46/7.50  
% 55.46/7.50  fof(f90,plain,(
% 55.46/7.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(equality_resolution,[],[f57])).
% 55.46/7.50  
% 55.46/7.50  fof(f8,conjecture,(
% 55.46/7.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f9,negated_conjecture,(
% 55.46/7.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 55.46/7.50    inference(negated_conjecture,[],[f8])).
% 55.46/7.50  
% 55.46/7.50  fof(f19,plain,(
% 55.46/7.50    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 55.46/7.50    inference(ennf_transformation,[],[f9])).
% 55.46/7.50  
% 55.46/7.50  fof(f20,plain,(
% 55.46/7.50    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 55.46/7.50    inference(flattening,[],[f19])).
% 55.46/7.50  
% 55.46/7.50  fof(f48,plain,(
% 55.46/7.50    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 55.46/7.50    inference(nnf_transformation,[],[f20])).
% 55.46/7.50  
% 55.46/7.50  fof(f49,plain,(
% 55.46/7.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 55.46/7.50    inference(flattening,[],[f48])).
% 55.46/7.50  
% 55.46/7.50  fof(f50,plain,(
% 55.46/7.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | ~r2_hidden(k4_tarski(sK10,sK11),sK12)) & (r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | r2_hidden(k4_tarski(sK10,sK11),sK12)) & r2_hidden(sK11,k3_relat_1(sK12)) & r2_hidden(sK10,k3_relat_1(sK12)) & v2_wellord1(sK12) & v1_relat_1(sK12))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f51,plain,(
% 55.46/7.50    (~r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | ~r2_hidden(k4_tarski(sK10,sK11),sK12)) & (r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | r2_hidden(k4_tarski(sK10,sK11),sK12)) & r2_hidden(sK11,k3_relat_1(sK12)) & r2_hidden(sK10,k3_relat_1(sK12)) & v2_wellord1(sK12) & v1_relat_1(sK12)),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f49,f50])).
% 55.46/7.50  
% 55.46/7.50  fof(f84,plain,(
% 55.46/7.50    v1_relat_1(sK12)),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f5,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f14,plain,(
% 55.46/7.50    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f5])).
% 55.46/7.50  
% 55.46/7.50  fof(f15,plain,(
% 55.46/7.50    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(flattening,[],[f14])).
% 55.46/7.50  
% 55.46/7.50  fof(f36,plain,(
% 55.46/7.50    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f15])).
% 55.46/7.50  
% 55.46/7.50  fof(f37,plain,(
% 55.46/7.50    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(rectify,[],[f36])).
% 55.46/7.50  
% 55.46/7.50  fof(f38,plain,(
% 55.46/7.50    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f39,plain,(
% 55.46/7.50    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f38])).
% 55.46/7.50  
% 55.46/7.50  fof(f70,plain,(
% 55.46/7.50    ( ! [X6,X4,X0,X5] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f39])).
% 55.46/7.50  
% 55.46/7.50  fof(f3,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f12,plain,(
% 55.46/7.50    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f3])).
% 55.46/7.50  
% 55.46/7.50  fof(f30,plain,(
% 55.46/7.50    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f12])).
% 55.46/7.50  
% 55.46/7.50  fof(f31,plain,(
% 55.46/7.50    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(flattening,[],[f30])).
% 55.46/7.50  
% 55.46/7.50  fof(f62,plain,(
% 55.46/7.50    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f31])).
% 55.46/7.50  
% 55.46/7.50  fof(f85,plain,(
% 55.46/7.50    v2_wellord1(sK12)),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f88,plain,(
% 55.46/7.50    r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | r2_hidden(k4_tarski(sK10,sK11),sK12)),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f7,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f18,plain,(
% 55.46/7.50    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f7])).
% 55.46/7.50  
% 55.46/7.50  fof(f44,plain,(
% 55.46/7.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f18])).
% 55.46/7.50  
% 55.46/7.50  fof(f45,plain,(
% 55.46/7.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(rectify,[],[f44])).
% 55.46/7.50  
% 55.46/7.50  fof(f46,plain,(
% 55.46/7.50    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK9(X0),sK8(X0)),X0) & ~r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & sK8(X0) != sK9(X0) & r2_hidden(sK9(X0),k3_relat_1(X0)) & r2_hidden(sK8(X0),k3_relat_1(X0))))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f47,plain,(
% 55.46/7.50    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK9(X0),sK8(X0)),X0) & ~r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & sK8(X0) != sK9(X0) & r2_hidden(sK9(X0),k3_relat_1(X0)) & r2_hidden(sK8(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f45,f46])).
% 55.46/7.50  
% 55.46/7.50  fof(f78,plain,(
% 55.46/7.50    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f47])).
% 55.46/7.50  
% 55.46/7.50  fof(f64,plain,(
% 55.46/7.50    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f31])).
% 55.46/7.50  
% 55.46/7.50  fof(f1,axiom,(
% 55.46/7.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f10,plain,(
% 55.46/7.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 55.46/7.50    inference(ennf_transformation,[],[f1])).
% 55.46/7.50  
% 55.46/7.50  fof(f21,plain,(
% 55.46/7.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 55.46/7.50    inference(nnf_transformation,[],[f10])).
% 55.46/7.50  
% 55.46/7.50  fof(f22,plain,(
% 55.46/7.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.46/7.50    inference(rectify,[],[f21])).
% 55.46/7.50  
% 55.46/7.50  fof(f23,plain,(
% 55.46/7.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f24,plain,(
% 55.46/7.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 55.46/7.50  
% 55.46/7.50  fof(f52,plain,(
% 55.46/7.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f24])).
% 55.46/7.50  
% 55.46/7.50  fof(f86,plain,(
% 55.46/7.50    r2_hidden(sK10,k3_relat_1(sK12))),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f55,plain,(
% 55.46/7.50    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f29])).
% 55.46/7.50  
% 55.46/7.50  fof(f92,plain,(
% 55.46/7.50    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(equality_resolution,[],[f55])).
% 55.46/7.50  
% 55.46/7.50  fof(f93,plain,(
% 55.46/7.50    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(equality_resolution,[],[f92])).
% 55.46/7.50  
% 55.46/7.50  fof(f87,plain,(
% 55.46/7.50    r2_hidden(sK11,k3_relat_1(sK12))),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f4,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f13,plain,(
% 55.46/7.50    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f4])).
% 55.46/7.50  
% 55.46/7.50  fof(f32,plain,(
% 55.46/7.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f13])).
% 55.46/7.50  
% 55.46/7.50  fof(f33,plain,(
% 55.46/7.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(rectify,[],[f32])).
% 55.46/7.50  
% 55.46/7.50  fof(f34,plain,(
% 55.46/7.50    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f35,plain,(
% 55.46/7.50    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 55.46/7.50  
% 55.46/7.50  fof(f67,plain,(
% 55.46/7.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f35])).
% 55.46/7.50  
% 55.46/7.50  fof(f61,plain,(
% 55.46/7.50    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f31])).
% 55.46/7.50  
% 55.46/7.50  fof(f6,axiom,(
% 55.46/7.50    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 55.46/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.46/7.50  
% 55.46/7.50  fof(f16,plain,(
% 55.46/7.50    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(ennf_transformation,[],[f6])).
% 55.46/7.50  
% 55.46/7.50  fof(f17,plain,(
% 55.46/7.50    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(flattening,[],[f16])).
% 55.46/7.50  
% 55.46/7.50  fof(f40,plain,(
% 55.46/7.50    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(nnf_transformation,[],[f17])).
% 55.46/7.50  
% 55.46/7.50  fof(f41,plain,(
% 55.46/7.50    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(rectify,[],[f40])).
% 55.46/7.50  
% 55.46/7.50  fof(f42,plain,(
% 55.46/7.50    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK6(X0) != sK7(X0) & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)))),
% 55.46/7.50    introduced(choice_axiom,[])).
% 55.46/7.50  
% 55.46/7.50  fof(f43,plain,(
% 55.46/7.50    ! [X0] : (((v4_relat_2(X0) | (sK6(X0) != sK7(X0) & r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 55.46/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).
% 55.46/7.50  
% 55.46/7.50  fof(f74,plain,(
% 55.46/7.50    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f43])).
% 55.46/7.50  
% 55.46/7.50  fof(f63,plain,(
% 55.46/7.50    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f31])).
% 55.46/7.50  
% 55.46/7.50  fof(f56,plain,(
% 55.46/7.50    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f29])).
% 55.46/7.50  
% 55.46/7.50  fof(f91,plain,(
% 55.46/7.50    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 55.46/7.50    inference(equality_resolution,[],[f56])).
% 55.46/7.50  
% 55.46/7.50  fof(f54,plain,(
% 55.46/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f24])).
% 55.46/7.50  
% 55.46/7.50  fof(f89,plain,(
% 55.46/7.50    ~r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) | ~r2_hidden(k4_tarski(sK10,sK11),sK12)),
% 55.46/7.50    inference(cnf_transformation,[],[f51])).
% 55.46/7.50  
% 55.46/7.50  fof(f53,plain,(
% 55.46/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 55.46/7.50    inference(cnf_transformation,[],[f24])).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1511,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.46/7.50      theory(equality) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_105192,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,X1)
% 55.46/7.50      | r2_hidden(X2,k1_wellord1(sK12,X3))
% 55.46/7.50      | X2 != X0
% 55.46/7.50      | k1_wellord1(sK12,X3) != X1 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1511]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_106665,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(sK12,X1))
% 55.46/7.50      | r2_hidden(X2,k1_wellord1(sK12,X1))
% 55.46/7.50      | X2 != X0
% 55.46/7.50      | k1_wellord1(sK12,X1) != k1_wellord1(sK12,X1) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_105192]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_108909,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(sK12,sK10))
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
% 55.46/7.50      | X0 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
% 55.46/7.50      | k1_wellord1(sK12,sK10) != k1_wellord1(sK12,sK10) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_106665]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_118839,plain,
% 55.46/7.50      ( ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
% 55.46/7.50      | r2_hidden(sK11,k1_wellord1(sK12,sK10))
% 55.46/7.50      | k1_wellord1(sK12,sK10) != k1_wellord1(sK12,sK10)
% 55.46/7.50      | sK11 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_108909]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1508,plain,( X0 = X0 ),theory(equality) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_50952,plain,
% 55.46/7.50      ( sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1508]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1985,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,X1)
% 55.46/7.50      | r2_hidden(X2,k1_wellord1(sK12,X3))
% 55.46/7.50      | X2 != X0
% 55.46/7.50      | k1_wellord1(sK12,X3) != X1 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1511]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_6777,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(sK12,X1))
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
% 55.46/7.50      | X0 != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
% 55.46/7.50      | k1_wellord1(sK12,X1) != k1_wellord1(sK12,sK10) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1985]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_15182,plain,
% 55.46/7.50      ( r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,X0))
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
% 55.46/7.50      | k1_wellord1(sK12,X0) != k1_wellord1(sK12,sK10)
% 55.46/7.50      | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_6777]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_38768,plain,
% 55.46/7.50      ( r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11))
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10))
% 55.46/7.50      | k1_wellord1(sK12,sK11) != k1_wellord1(sK12,sK10)
% 55.46/7.50      | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_15182]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_38769,plain,
% 55.46/7.50      ( k1_wellord1(sK12,sK11) != k1_wellord1(sK12,sK10)
% 55.46/7.50      | sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) = iProver_top
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_38768]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1512,plain,
% 55.46/7.50      ( X0 != X1 | X2 != X3 | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
% 55.46/7.50      theory(equality) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_14508,plain,
% 55.46/7.50      ( k1_wellord1(sK12,sK11) = k1_wellord1(sK12,X0)
% 55.46/7.50      | sK11 != X0
% 55.46/7.50      | sK12 != sK12 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1512]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_38514,plain,
% 55.46/7.50      ( k1_wellord1(sK12,sK11) = k1_wellord1(sK12,sK10)
% 55.46/7.50      | sK11 != sK10
% 55.46/7.50      | sK12 != sK12 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_14508]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_30784,plain,
% 55.46/7.50      ( k1_wellord1(sK12,sK10) = k1_wellord1(sK12,sK10) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1508]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_6,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | ~ v1_relat_1(X1)
% 55.46/7.50      | X0 = X2 ),
% 55.46/7.50      inference(cnf_transformation,[],[f90]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_37,negated_conjecture,
% 55.46/7.50      ( v1_relat_1(sK12) ),
% 55.46/7.50      inference(cnf_transformation,[],[f84]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1193,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | X2 = X0
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_6,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1194,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(sK12,X1))
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1193]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_15169,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),X0),sK12)
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,X0))
% 55.46/7.50      | X0 = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1194]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_29288,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK11),sK12)
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11))
% 55.46/7.50      | sK11 = sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_15169]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_21,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 55.46/7.50      | r2_hidden(k4_tarski(X3,X1),X2)
% 55.46/7.50      | ~ v8_relat_2(X2)
% 55.46/7.50      | ~ v1_relat_1(X2) ),
% 55.46/7.50      inference(cnf_transformation,[],[f70]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1223,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 55.46/7.50      | r2_hidden(k4_tarski(X3,X1),X2)
% 55.46/7.50      | ~ v8_relat_2(X2)
% 55.46/7.50      | sK12 != X2 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_21,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1224,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X1),sK12)
% 55.46/7.50      | ~ v8_relat_2(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1223]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_13,plain,
% 55.46/7.50      ( v8_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 55.46/7.50      inference(cnf_transformation,[],[f62]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_36,negated_conjecture,
% 55.46/7.50      ( v2_wellord1(sK12) ),
% 55.46/7.50      inference(cnf_transformation,[],[f85]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_501,plain,
% 55.46/7.50      ( v8_relat_2(X0) | ~ v1_relat_1(X0) | sK12 != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_13,c_36]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_502,plain,
% 55.46/7.50      ( v8_relat_2(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_501]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_97,plain,
% 55.46/7.50      ( v8_relat_2(sK12) | ~ v2_wellord1(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_13]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_504,plain,
% 55.46/7.50      ( v8_relat_2(sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_502,c_37,c_36,c_97]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_840,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 55.46/7.50      | r2_hidden(k4_tarski(X3,X1),X2)
% 55.46/7.50      | ~ v1_relat_1(X2)
% 55.46/7.50      | sK12 != X2 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_21,c_504]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_841,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X1),sK12)
% 55.46/7.50      | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_840]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_843,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X2,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_841,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_844,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X1),sK12) ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_843]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1226,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X2,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_1224,c_37,c_841]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1227,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X2,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X1),sK12) ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_1226]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_3956,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X0,sK11),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1227]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_13119,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK11),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_3956]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_33,negated_conjecture,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(cnf_transformation,[],[f88]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1912,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_31,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 55.46/7.50      | ~ v6_relat_2(X1)
% 55.46/7.50      | ~ v1_relat_1(X1)
% 55.46/7.50      | X0 = X2 ),
% 55.46/7.50      inference(cnf_transformation,[],[f78]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1137,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 55.46/7.50      | ~ v6_relat_2(X1)
% 55.46/7.50      | X2 = X0
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1138,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | ~ r2_hidden(X1,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ v6_relat_2(sK12)
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1137]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_11,plain,
% 55.46/7.50      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 55.46/7.50      inference(cnf_transformation,[],[f64]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_523,plain,
% 55.46/7.50      ( v6_relat_2(X0) | ~ v1_relat_1(X0) | sK12 != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_11,c_36]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_524,plain,
% 55.46/7.50      ( v6_relat_2(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_523]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_103,plain,
% 55.46/7.50      ( v6_relat_2(sK12) | ~ v2_wellord1(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_11]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_526,plain,
% 55.46/7.50      ( v6_relat_2(sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_524,c_37,c_36,c_103]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1000,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 55.46/7.50      | ~ v1_relat_1(X1)
% 55.46/7.50      | X2 = X0
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_31,c_526]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1001,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | ~ r2_hidden(X1,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ v1_relat_1(sK12)
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1000]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1140,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(X1,k3_relat_1(sK12))
% 55.46/7.50      | ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_1138,c_37,c_1001]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1141,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | ~ r2_hidden(X1,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_1140]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1906,plain,
% 55.46/7.50      ( X0 = X1
% 55.46/7.50      | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1900,plain,
% 55.46/7.50      ( X0 = X1
% 55.46/7.50      | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_3116,plain,
% 55.46/7.50      ( X0 = X1
% 55.46/7.50      | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
% 55.46/7.50      | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_1906,c_1900]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_7763,plain,
% 55.46/7.50      ( X0 = X1
% 55.46/7.50      | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
% 55.46/7.50      | r2_hidden(X0,k1_wellord1(sK12,X1)) = iProver_top
% 55.46/7.50      | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_3116,c_1900]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 55.46/7.50      inference(cnf_transformation,[],[f52]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1914,plain,
% 55.46/7.50      ( r2_hidden(X0,X1) != iProver_top
% 55.46/7.50      | r2_hidden(X0,X2) = iProver_top
% 55.46/7.50      | r1_tarski(X1,X2) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_8966,plain,
% 55.46/7.50      ( X0 = X1
% 55.46/7.50      | r2_hidden(X1,X2) = iProver_top
% 55.46/7.50      | r2_hidden(X0,k1_wellord1(sK12,X1)) = iProver_top
% 55.46/7.50      | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r1_tarski(k1_wellord1(sK12,X0),X2) != iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_7763,c_1914]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10565,plain,
% 55.46/7.50      ( sK10 = X0
% 55.46/7.50      | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
% 55.46/7.50      | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_1912,c_8966]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_35,negated_conjecture,
% 55.46/7.50      ( r2_hidden(sK10,k3_relat_1(sK12)) ),
% 55.46/7.50      inference(cnf_transformation,[],[f86]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_40,plain,
% 55.46/7.50      ( r2_hidden(sK10,k3_relat_1(sK12)) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10571,plain,
% 55.46/7.50      ( r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
% 55.46/7.50      | sK10 = X0 ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_10565,c_40]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10572,plain,
% 55.46/7.50      ( sK10 = X0
% 55.46/7.50      | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
% 55.46/7.50      | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_10571]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_8,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 55.46/7.50      inference(cnf_transformation,[],[f93]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1174,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_8,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1175,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(sK12,X0)) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1174]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1902,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(sK12,X0)) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10589,plain,
% 55.46/7.50      ( sK11 = sK10
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(sK11,k3_relat_1(sK12)) != iProver_top
% 55.46/7.50      | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_10572,c_1902]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_34,negated_conjecture,
% 55.46/7.50      ( r2_hidden(sK11,k3_relat_1(sK12)) ),
% 55.46/7.50      inference(cnf_transformation,[],[f87]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_41,plain,
% 55.46/7.50      ( r2_hidden(sK11,k3_relat_1(sK12)) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1523,plain,
% 55.46/7.50      ( sK12 = sK12 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1508]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_17,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 55.46/7.50      | ~ v1_relat_2(X1)
% 55.46/7.50      | ~ v1_relat_1(X1) ),
% 55.46/7.50      inference(cnf_transformation,[],[f67]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1160,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 55.46/7.50      | ~ v1_relat_2(X1)
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1161,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),sK12)
% 55.46/7.50      | ~ v1_relat_2(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1160]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_14,plain,
% 55.46/7.50      ( v1_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 55.46/7.50      inference(cnf_transformation,[],[f61]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_490,plain,
% 55.46/7.50      ( v1_relat_2(X0) | ~ v1_relat_1(X0) | sK12 != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_491,plain,
% 55.46/7.50      ( v1_relat_2(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_490]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_94,plain,
% 55.46/7.50      ( v1_relat_2(sK12) | ~ v2_wellord1(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_14]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_493,plain,
% 55.46/7.50      ( v1_relat_2(sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_491,c_37,c_36,c_94]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_578,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 55.46/7.50      | ~ v1_relat_1(X1)
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_17,c_493]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_579,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),sK12)
% 55.46/7.50      | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_578]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_583,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X0,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_579,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_584,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),sK12) ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_583]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1163,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(X0,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_1161,c_37,c_579]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1164,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k3_relat_1(sK12))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X0),sK12) ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_1163]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1969,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(sK10,k3_relat_1(sK12)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1164]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1970,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK10),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_1969]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1951,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,X1)
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | k4_tarski(sK10,sK11) != X0
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1511]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2015,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK10,sK10),sK12)
% 55.46/7.50      | k4_tarski(sK10,sK11) != k4_tarski(sK10,sK10)
% 55.46/7.50      | sK12 != sK12 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1951]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2016,plain,
% 55.46/7.50      ( k4_tarski(sK10,sK11) != k4_tarski(sK10,sK10)
% 55.46/7.50      | sK12 != sK12
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK10),sK12) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1514,plain,
% 55.46/7.50      ( X0 != X1 | X2 != X3 | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
% 55.46/7.50      theory(equality) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2072,plain,
% 55.46/7.50      ( k4_tarski(sK10,sK11) = k4_tarski(sK10,sK10)
% 55.46/7.50      | sK11 != sK10
% 55.46/7.50      | sK10 != sK10 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1514]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_25,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 55.46/7.50      | ~ v4_relat_2(X2)
% 55.46/7.50      | ~ v1_relat_1(X2)
% 55.46/7.50      | X0 = X1 ),
% 55.46/7.50      inference(cnf_transformation,[],[f74]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1206,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 55.46/7.50      | ~ v4_relat_2(X2)
% 55.46/7.50      | X1 = X0
% 55.46/7.50      | sK12 != X2 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1207,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | ~ v4_relat_2(sK12)
% 55.46/7.50      | X0 = X1 ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1206]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_12,plain,
% 55.46/7.50      ( v4_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 55.46/7.50      inference(cnf_transformation,[],[f63]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_512,plain,
% 55.46/7.50      ( v4_relat_2(X0) | ~ v1_relat_1(X0) | sK12 != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_12,c_36]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_513,plain,
% 55.46/7.50      ( v4_relat_2(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_512]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_100,plain,
% 55.46/7.50      ( v4_relat_2(sK12) | ~ v2_wellord1(sK12) | ~ v1_relat_1(sK12) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_12]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_515,plain,
% 55.46/7.50      ( v4_relat_2(sK12) ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_513,c_37,c_36,c_100]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_744,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 55.46/7.50      | ~ v1_relat_1(X2)
% 55.46/7.50      | X1 = X0
% 55.46/7.50      | sK12 != X2 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_25,c_515]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_745,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | ~ v1_relat_1(sK12)
% 55.46/7.50      | X0 = X1 ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_744]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1209,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | X0 = X1 ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_1207,c_37,c_745]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1210,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(X1,X0),sK12)
% 55.46/7.50      | X1 = X0 ),
% 55.46/7.50      inference(renaming,[status(thm)],[c_1209]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2302,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(X0,sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK10,X0),sK12)
% 55.46/7.50      | X0 = sK10 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1210]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2918,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK10),sK12) | sK10 = sK10 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_2302]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10742,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
% 55.46/7.50      | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_10589,c_35,c_40,c_41,c_1523,c_1969,c_1970,c_2016,
% 55.46/7.50                 c_2072,c_2918]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10747,plain,
% 55.46/7.50      ( sK11 = sK10
% 55.46/7.50      | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_10742,c_1900]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_7,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | ~ v1_relat_1(X1) ),
% 55.46/7.50      inference(cnf_transformation,[],[f91]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1183,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 55.46/7.50      | sK12 != X1 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_7,c_37]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1184,plain,
% 55.46/7.50      ( ~ r2_hidden(X0,k1_wellord1(sK12,X1))
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_1183]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1901,plain,
% 55.46/7.50      ( r2_hidden(X0,k1_wellord1(sK12,X1)) != iProver_top
% 55.46/7.50      | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10911,plain,
% 55.46/7.50      ( sK11 = sK10
% 55.46/7.50      | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
% 55.46/7.50      inference(superposition,[status(thm)],[c_10747,c_1901]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10917,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
% 55.46/7.50      inference(global_propositional_subsumption,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_10911,c_35,c_40,c_1523,c_1969,c_1970,c_2016,c_2072,
% 55.46/7.50                 c_2918]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_10919,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) ),
% 55.46/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_10917]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_6810,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1184]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_4691,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK11,sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | sK11 = sK10 ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_2302]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_2816,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK11,X0),sK12)
% 55.46/7.50      | ~ r2_hidden(sK11,k1_wellord1(sK12,X0)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_1184]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_4690,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK11,sK10),sK12)
% 55.46/7.50      | ~ r2_hidden(sK11,k1_wellord1(sK12,sK10)) ),
% 55.46/7.50      inference(instantiation,[status(thm)],[c_2816]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_0,plain,
% 55.46/7.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 55.46/7.50      inference(cnf_transformation,[],[f54]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_32,negated_conjecture,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(cnf_transformation,[],[f89]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_291,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(prop_impl,[status(thm)],[c_32]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_643,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | ~ r2_hidden(sK0(X0,X1),X1)
% 55.46/7.50      | k1_wellord1(sK12,sK11) != X1
% 55.46/7.50      | k1_wellord1(sK12,sK10) != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_0,c_291]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_644,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | ~ r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_643]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_645,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK11)) != iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_1,plain,
% 55.46/7.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 55.46/7.50      inference(cnf_transformation,[],[f53]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_633,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | r2_hidden(sK0(X0,X1),X0)
% 55.46/7.50      | k1_wellord1(sK12,sK11) != X1
% 55.46/7.50      | k1_wellord1(sK12,sK10) != X0 ),
% 55.46/7.50      inference(resolution_lifted,[status(thm)],[c_1,c_291]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_634,plain,
% 55.46/7.50      ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) ),
% 55.46/7.50      inference(unflattening,[status(thm)],[c_633]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(c_635,plain,
% 55.46/7.50      ( r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top
% 55.46/7.50      | r2_hidden(sK0(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)),k1_wellord1(sK12,sK10)) = iProver_top ),
% 55.46/7.50      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 55.46/7.50  
% 55.46/7.50  cnf(contradiction,plain,
% 55.46/7.50      ( $false ),
% 55.46/7.50      inference(minisat,
% 55.46/7.50                [status(thm)],
% 55.46/7.50                [c_118839,c_50952,c_38769,c_38514,c_30784,c_29288,
% 55.46/7.50                 c_13119,c_10919,c_10917,c_6810,c_4691,c_4690,c_1523,
% 55.46/7.50                 c_645,c_644,c_635,c_634]) ).
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.46/7.50  
% 55.46/7.50  ------                               Statistics
% 55.46/7.50  
% 55.46/7.50  ------ General
% 55.46/7.50  
% 55.46/7.50  abstr_ref_over_cycles:                  0
% 55.46/7.50  abstr_ref_under_cycles:                 0
% 55.46/7.50  gc_basic_clause_elim:                   0
% 55.46/7.50  forced_gc_time:                         0
% 55.46/7.50  parsing_time:                           0.009
% 55.46/7.50  unif_index_cands_time:                  0.
% 55.46/7.50  unif_index_add_time:                    0.
% 55.46/7.50  orderings_time:                         0.
% 55.46/7.50  out_proof_time:                         0.018
% 55.46/7.50  total_time:                             6.87
% 55.46/7.50  num_of_symbols:                         56
% 55.46/7.50  num_of_terms:                           78252
% 55.46/7.50  
% 55.46/7.50  ------ Preprocessing
% 55.46/7.50  
% 55.46/7.50  num_of_splits:                          0
% 55.46/7.50  num_of_split_atoms:                     0
% 55.46/7.50  num_of_reused_defs:                     0
% 55.46/7.50  num_eq_ax_congr_red:                    26
% 55.46/7.50  num_of_sem_filtered_clauses:            1
% 55.46/7.50  num_of_subtypes:                        0
% 55.46/7.50  monotx_restored_types:                  0
% 55.46/7.50  sat_num_of_epr_types:                   0
% 55.46/7.50  sat_num_of_non_cyclic_types:            0
% 55.46/7.50  sat_guarded_non_collapsed_types:        0
% 55.46/7.50  num_pure_diseq_elim:                    0
% 55.46/7.50  simp_replaced_by:                       0
% 55.46/7.50  res_preprocessed:                       106
% 55.46/7.50  prep_upred:                             0
% 55.46/7.50  prep_unflattend:                        64
% 55.46/7.50  smt_new_axioms:                         0
% 55.46/7.50  pred_elim_cands:                        2
% 55.46/7.50  pred_elim:                              7
% 55.46/7.50  pred_elim_cl:                           21
% 55.46/7.50  pred_elim_cycles:                       14
% 55.46/7.50  merged_defs:                            8
% 55.46/7.50  merged_defs_ncl:                        0
% 55.46/7.50  bin_hyper_res:                          8
% 55.46/7.50  prep_cycles:                            4
% 55.46/7.50  pred_elim_time:                         0.015
% 55.46/7.50  splitting_time:                         0.
% 55.46/7.50  sem_filter_time:                        0.
% 55.46/7.50  monotx_time:                            0.
% 55.46/7.50  subtype_inf_time:                       0.
% 55.46/7.50  
% 55.46/7.50  ------ Problem properties
% 55.46/7.50  
% 55.46/7.50  clauses:                                17
% 55.46/7.50  conjectures:                            4
% 55.46/7.50  epr:                                    1
% 55.46/7.50  horn:                                   10
% 55.46/7.50  ground:                                 4
% 55.46/7.50  unary:                                  3
% 55.46/7.50  binary:                                 6
% 55.46/7.50  lits:                                   42
% 55.46/7.50  lits_eq:                                8
% 55.46/7.50  fd_pure:                                0
% 55.46/7.50  fd_pseudo:                              0
% 55.46/7.50  fd_cond:                                0
% 55.46/7.50  fd_pseudo_cond:                         5
% 55.46/7.50  ac_symbols:                             0
% 55.46/7.50  
% 55.46/7.50  ------ Propositional Solver
% 55.46/7.50  
% 55.46/7.50  prop_solver_calls:                      56
% 55.46/7.50  prop_fast_solver_calls:                 4632
% 55.46/7.50  smt_solver_calls:                       0
% 55.46/7.50  smt_fast_solver_calls:                  0
% 55.46/7.50  prop_num_of_clauses:                    54586
% 55.46/7.50  prop_preprocess_simplified:             67887
% 55.46/7.50  prop_fo_subsumed:                       233
% 55.46/7.50  prop_solver_time:                       0.
% 55.46/7.50  smt_solver_time:                        0.
% 55.46/7.50  smt_fast_solver_time:                   0.
% 55.46/7.50  prop_fast_solver_time:                  0.
% 55.46/7.50  prop_unsat_core_time:                   0.004
% 55.46/7.50  
% 55.46/7.50  ------ QBF
% 55.46/7.50  
% 55.46/7.50  qbf_q_res:                              0
% 55.46/7.50  qbf_num_tautologies:                    0
% 55.46/7.50  qbf_prep_cycles:                        0
% 55.46/7.50  
% 55.46/7.50  ------ BMC1
% 55.46/7.50  
% 55.46/7.50  bmc1_current_bound:                     -1
% 55.46/7.50  bmc1_last_solved_bound:                 -1
% 55.46/7.50  bmc1_unsat_core_size:                   -1
% 55.46/7.50  bmc1_unsat_core_parents_size:           -1
% 55.46/7.50  bmc1_merge_next_fun:                    0
% 55.46/7.50  bmc1_unsat_core_clauses_time:           0.
% 55.46/7.50  
% 55.46/7.50  ------ Instantiation
% 55.46/7.50  
% 55.46/7.50  inst_num_of_clauses:                    759
% 55.46/7.50  inst_num_in_passive:                    301
% 55.46/7.50  inst_num_in_active:                     2460
% 55.46/7.50  inst_num_in_unprocessed:                168
% 55.46/7.50  inst_num_of_loops:                      3301
% 55.46/7.50  inst_num_of_learning_restarts:          1
% 55.46/7.50  inst_num_moves_active_passive:          838
% 55.46/7.50  inst_lit_activity:                      0
% 55.46/7.50  inst_lit_activity_moves:                2
% 55.46/7.50  inst_num_tautologies:                   0
% 55.46/7.50  inst_num_prop_implied:                  0
% 55.46/7.50  inst_num_existing_simplified:           0
% 55.46/7.50  inst_num_eq_res_simplified:             0
% 55.46/7.50  inst_num_child_elim:                    0
% 55.46/7.50  inst_num_of_dismatching_blockings:      14489
% 55.46/7.50  inst_num_of_non_proper_insts:           10302
% 55.46/7.50  inst_num_of_duplicates:                 0
% 55.46/7.50  inst_inst_num_from_inst_to_res:         0
% 55.46/7.50  inst_dismatching_checking_time:         0.
% 55.46/7.50  
% 55.46/7.50  ------ Resolution
% 55.46/7.50  
% 55.46/7.50  res_num_of_clauses:                     25
% 55.46/7.50  res_num_in_passive:                     25
% 55.46/7.50  res_num_in_active:                      0
% 55.46/7.50  res_num_of_loops:                       110
% 55.46/7.50  res_forward_subset_subsumed:            541
% 55.46/7.50  res_backward_subset_subsumed:           2
% 55.46/7.50  res_forward_subsumed:                   0
% 55.46/7.50  res_backward_subsumed:                  0
% 55.46/7.50  res_forward_subsumption_resolution:     0
% 55.46/7.50  res_backward_subsumption_resolution:    0
% 55.46/7.50  res_clause_to_clause_subsumption:       407547
% 55.46/7.50  res_orphan_elimination:                 0
% 55.46/7.50  res_tautology_del:                      1466
% 55.46/7.50  res_num_eq_res_simplified:              0
% 55.46/7.50  res_num_sel_changes:                    0
% 55.46/7.50  res_moves_from_active_to_pass:          0
% 55.46/7.50  
% 55.46/7.50  ------ Superposition
% 55.46/7.50  
% 55.46/7.50  sup_time_total:                         0.
% 55.46/7.50  sup_time_generating:                    0.
% 55.46/7.50  sup_time_sim_full:                      0.
% 55.46/7.50  sup_time_sim_immed:                     0.
% 55.46/7.50  
% 55.46/7.50  sup_num_of_clauses:                     12363
% 55.46/7.50  sup_num_in_active:                      531
% 55.46/7.50  sup_num_in_passive:                     11832
% 55.46/7.50  sup_num_of_loops:                       660
% 55.46/7.50  sup_fw_superposition:                   12327
% 55.46/7.50  sup_bw_superposition:                   17777
% 55.46/7.50  sup_immediate_simplified:               13042
% 55.46/7.50  sup_given_eliminated:                   0
% 55.46/7.50  comparisons_done:                       0
% 55.46/7.50  comparisons_avoided:                    31
% 55.46/7.50  
% 55.46/7.50  ------ Simplifications
% 55.46/7.50  
% 55.46/7.50  
% 55.46/7.50  sim_fw_subset_subsumed:                 5111
% 55.46/7.50  sim_bw_subset_subsumed:                 1940
% 55.46/7.50  sim_fw_subsumed:                        5921
% 55.46/7.50  sim_bw_subsumed:                        276
% 55.46/7.50  sim_fw_subsumption_res:                 0
% 55.46/7.50  sim_bw_subsumption_res:                 0
% 55.46/7.50  sim_tautology_del:                      38
% 55.46/7.50  sim_eq_tautology_del:                   928
% 55.46/7.50  sim_eq_res_simp:                        66
% 55.46/7.50  sim_fw_demodulated:                     0
% 55.46/7.50  sim_bw_demodulated:                     0
% 55.46/7.50  sim_light_normalised:                   0
% 55.46/7.50  sim_joinable_taut:                      0
% 55.46/7.50  sim_joinable_simp:                      0
% 55.46/7.50  sim_ac_normalised:                      0
% 55.46/7.50  sim_smt_subsumption:                    0
% 55.46/7.50  
%------------------------------------------------------------------------------
