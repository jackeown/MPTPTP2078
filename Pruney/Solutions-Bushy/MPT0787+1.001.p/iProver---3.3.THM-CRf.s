%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  190 (2381 expanded)
%              Number of clauses        :  115 ( 584 expanded)
%              Number of leaves         :   15 ( 410 expanded)
%              Depth                    :   35
%              Number of atoms          :  824 (15593 expanded)
%              Number of equality atoms :  204 (2045 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
          | sK0(X0,X1,X2) = X1
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
            & sK0(X0,X1,X2) != X1 )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                | sK0(X0,X1,X2) = X1
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                  & sK0(X0,X1,X2) != X1 )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

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

fof(f64,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    v2_wellord1(sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f88,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f51])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f93,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f87,plain,(
    r2_hidden(sK11,k3_relat_1(sK12)) ),
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

fof(f62,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,
    ( ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f51])).

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

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1917,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1182,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_37])).

cnf(c_1183,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK12,X1))
    | r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(unflattening,[status(thm)],[c_1182])).

cnf(c_1903,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_2417,plain,
    ( r1_tarski(k1_wellord1(sK12,X0),X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK12,X0),X1),X0),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1903])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1136,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_1137,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ v6_relat_2(sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1136])).

cnf(c_11,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,negated_conjecture,
    ( v2_wellord1(sK12) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_524,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_525,plain,
    ( v6_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_103,plain,
    ( v6_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_527,plain,
    ( v6_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_37,c_36,c_103])).

cnf(c_999,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_527])).

cnf(c_1000,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ v1_relat_1(sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_1002,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK12)
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | ~ r2_hidden(X0,k3_relat_1(sK12))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_37])).

cnf(c_1003,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1002])).

cnf(c_1139,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK12)
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | ~ r2_hidden(X0,k3_relat_1(sK12))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1137,c_37,c_1000])).

cnf(c_1140,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | ~ r2_hidden(X1,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X1,X0),sK12)
    | r2_hidden(k4_tarski(X0,X1),sK12)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1139])).

cnf(c_1908,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1192,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_37])).

cnf(c_1193,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1192])).

cnf(c_1902,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_3011,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1902])).

cnf(c_4725,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3011,c_1902])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1914,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1916,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2629,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1916])).

cnf(c_4913,plain,
    ( sK10 = X0
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_2629])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( r2_hidden(sK10,k3_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5731,plain,
    ( r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | sK10 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4913,c_40])).

cnf(c_5732,plain,
    ( sK10 = X0
    | r2_hidden(X0,k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5731])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1173,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_1174,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK12,X0)) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1904,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1174])).

cnf(c_5751,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top
    | r2_hidden(sK11,k3_relat_1(sK12)) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5732,c_1904])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK11,k3_relat_1(sK12)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( r2_hidden(sK11,k3_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2815,plain,
    ( r2_hidden(X0,k1_wellord1(sK12,sK11))
    | ~ r2_hidden(k4_tarski(X0,sK11),sK12)
    | sK11 = X0 ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_4063,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK11),sK12)
    | r2_hidden(sK10,k1_wellord1(sK12,sK11))
    | sK11 = sK10 ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_4066,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4063])).

cnf(c_6200,plain,
    ( sK11 = sK10
    | r2_hidden(sK10,k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5751,c_41,c_4066])).

cnf(c_6206,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK10,sK11),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_6200,c_1903])).

cnf(c_21,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1222,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_1223,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ v8_relat_2(sK12) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_13,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_502,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_503,plain,
    ( v8_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_97,plain,
    ( v8_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_505,plain,
    ( v8_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_37,c_36,c_97])).

cnf(c_839,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_505])).

cnf(c_840,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_842,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_840,c_37])).

cnf(c_843,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12) ),
    inference(renaming,[status(thm)],[c_842])).

cnf(c_1225,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1223,c_37,c_840])).

cnf(c_1226,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X2,X0),sK12)
    | r2_hidden(k4_tarski(X2,X1),sK12) ),
    inference(renaming,[status(thm)],[c_1225])).

cnf(c_1909,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK12) != iProver_top
    | r2_hidden(k4_tarski(X2,X1),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_6213,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(X0,sK11),sK12) = iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_6206,c_1909])).

cnf(c_6511,plain,
    ( sK11 = sK10
    | r1_tarski(k1_wellord1(sK12,sK10),X0) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK12,sK10),X0),sK11),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_6213])).

cnf(c_7662,plain,
    ( sK1(k1_wellord1(sK12,sK10),X0) = sK11
    | sK11 = sK10
    | r1_tarski(k1_wellord1(sK12,sK10),X0) = iProver_top
    | r2_hidden(sK1(k1_wellord1(sK12,sK10),X0),k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6511,c_1902])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1918,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8384,plain,
    ( sK1(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = sK11
    | sK11 = sK10
    | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7662,c_1918])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11))
    | ~ r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_43,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9598,plain,
    ( sK11 = sK10
    | sK1(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = sK11 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8384,c_43,c_6206])).

cnf(c_9599,plain,
    ( sK1(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = sK11
    | sK11 = sK10 ),
    inference(renaming,[status(thm)],[c_9598])).

cnf(c_9603,plain,
    ( sK11 = sK10
    | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(sK11,k1_wellord1(sK12,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9599,c_1917])).

cnf(c_25,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1205,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | X1 = X0
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_1206,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ v4_relat_2(sK12)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1205])).

cnf(c_12,plain,
    ( v4_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_513,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_514,plain,
    ( v4_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_100,plain,
    ( v4_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_516,plain,
    ( v4_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_37,c_36,c_100])).

cnf(c_743,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_516])).

cnf(c_744,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ v1_relat_1(sK12)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_1208,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_37,c_744])).

cnf(c_1209,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),sK12)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1208])).

cnf(c_1910,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_6214,plain,
    ( sK11 = sK10
    | r2_hidden(k4_tarski(sK11,sK10),sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_6206,c_1910])).

cnf(c_9609,plain,
    ( sK11 = sK10
    | r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK10),sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_9599,c_2417])).

cnf(c_9711,plain,
    ( sK11 = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9603,c_43,c_6206,c_6214,c_9609])).

cnf(c_1915,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK11),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9740,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK10),sK12) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9711,c_1915])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1159,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1160,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ v1_relat_2(sK12) ),
    inference(unflattening,[status(thm)],[c_1159])).

cnf(c_14,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_491,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_492,plain,
    ( v1_relat_2(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_94,plain,
    ( v1_relat_2(sK12)
    | ~ v2_wellord1(sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_494,plain,
    ( v1_relat_2(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_37,c_36,c_94])).

cnf(c_579,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_494])).

cnf(c_580,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_37])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12) ),
    inference(renaming,[status(thm)],[c_584])).

cnf(c_1162,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK12)
    | ~ r2_hidden(X0,k3_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_37,c_580])).

cnf(c_1163,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,X0),sK12) ),
    inference(renaming,[status(thm)],[c_1162])).

cnf(c_2042,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),sK12)
    | ~ r2_hidden(sK10,k3_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_2043,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),sK12) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2042])).

cnf(c_9969,plain,
    ( r1_tarski(k1_wellord1(sK12,sK10),k1_wellord1(sK12,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9740,c_40,c_2043])).

cnf(c_2424,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_1918])).

cnf(c_9974,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9969,c_2424])).


%------------------------------------------------------------------------------
