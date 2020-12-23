%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:30 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  213 (5043 expanded)
%              Number of clauses        :  132 (1309 expanded)
%              Number of leaves         :   22 ( 928 expanded)
%              Depth                    :   34
%              Number of atoms          :  820 (30640 expanded)
%              Number of equality atoms :  269 (4662 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
        | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
        | r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & r2_hidden(sK6,k3_relat_1(sK7))
      & r2_hidden(sK5,k3_relat_1(sK7))
      & v2_wellord1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
      | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
      | r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & r2_hidden(sK6,k3_relat_1(sK7))
    & r2_hidden(sK5,k3_relat_1(sK7))
    & v2_wellord1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f51,f52])).

fof(f91,plain,
    ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f98,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f8,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f48])).

fof(f77,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,
    ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    r2_hidden(sK5,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2103,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2128,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2127,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4982,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_2127])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_515,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_518,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_38])).

cnf(c_2097,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),X1) = k1_wellord1(sK7,X1)
    | r2_hidden(X1,k1_wellord1(sK7,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_8551,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(X1,X2)) = k1_wellord1(sK7,sK0(X1,X2))
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(X1,k1_wellord1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4982,c_2097])).

cnf(c_9275,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),X0)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2103,c_8551])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2120,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9533,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),X0)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))
    | sK6 = sK5
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_9275,c_2120])).

cnf(c_39,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1325,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3317,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2791,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_3698,plain,
    ( X0 != sK6
    | X0 = sK5
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_6324,plain,
    ( sK6 != sK6
    | sK6 = sK5
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_2881,plain,
    ( r2_hidden(X0,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

cnf(c_6930,plain,
    ( r2_hidden(X0,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_10,c_2881])).

cnf(c_7187,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
    | r2_hidden(X0,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6930,c_38])).

cnf(c_7188,plain,
    ( r2_hidden(X0,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(renaming,[status(thm)],[c_7187])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7475,plain,
    ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_7188,c_12])).

cnf(c_8424,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | sK5 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7475,c_38])).

cnf(c_8425,plain,
    ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(renaming,[status(thm)],[c_8424])).

cnf(c_8426,plain,
    ( sK5 = sK6
    | r2_hidden(sK6,k1_wellord1(sK7,sK5)) != iProver_top
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8425])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3182,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r1_tarski(X0,k1_wellord1(sK7,sK6))
    | ~ r1_tarski(X0,k1_wellord1(sK7,sK5)) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

cnf(c_6931,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | r1_tarski(X0,k1_wellord1(sK7,sK6))
    | ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_10,c_3182])).

cnf(c_7486,plain,
    ( ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
    | r1_tarski(X0,k1_wellord1(sK7,sK6))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6931,c_38])).

cnf(c_7487,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | r1_tarski(X0,k1_wellord1(sK7,sK6))
    | ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
    | sK5 = sK6 ),
    inference(renaming,[status(thm)],[c_7486])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7518,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5))
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_7487,c_33])).

cnf(c_2506,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7760,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | sK5 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7518,c_38,c_2506])).

cnf(c_7761,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(renaming,[status(thm)],[c_7760])).

cnf(c_9072,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK7)
    | ~ r2_hidden(sK6,k3_relat_1(sK7))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(sK5,k3_relat_1(sK7))
    | ~ v6_relat_2(sK7)
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_28,c_7761])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK5,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_15,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_97,plain,
    ( v6_relat_2(sK7)
    | ~ v2_wellord1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_9404,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK6,sK5),sK7)
    | sK5 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9072,c_38,c_37,c_36,c_35,c_97])).

cnf(c_9405,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK7)
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | sK5 = sK6 ),
    inference(renaming,[status(thm)],[c_9404])).

cnf(c_9636,plain,
    ( r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | r2_hidden(sK5,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7)
    | sK6 = sK5
    | sK5 = sK6 ),
    inference(resolution,[status(thm)],[c_9405,c_10])).

cnf(c_9637,plain,
    ( sK6 = sK5
    | sK5 = sK6
    | r2_hidden(sK6,k1_wellord1(sK7,sK5)) = iProver_top
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9636])).

cnf(c_10237,plain,
    ( sK6 = sK5
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9533,c_39,c_3317,c_6324,c_8426,c_9637])).

cnf(c_10245,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK5) = k1_wellord1(sK7,sK5)
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_10237,c_2097])).

cnf(c_29,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2107,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2100,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2118,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8548,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_wellord1(X2,sK0(X0,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4982,c_2118])).

cnf(c_13022,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1)))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1))))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9275,c_8548])).

cnf(c_14250,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0)))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_13022])).

cnf(c_14285,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1)))))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1))))))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14250,c_8548])).

cnf(c_1327,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5277,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1327,c_1325])).

cnf(c_10814,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | r1_tarski(k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0),X2)
    | ~ r1_tarski(k1_wellord1(sK7,X0),X2) ),
    inference(resolution,[status(thm)],[c_5277,c_518])).

cnf(c_11587,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | r1_tarski(X2,X3)
    | ~ r1_tarski(X2,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0))
    | ~ r1_tarski(k1_wellord1(sK7,X0),X3) ),
    inference(resolution,[status(thm)],[c_10814,c_6])).

cnf(c_5281,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | r1_tarski(X2,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0))
    | ~ r1_tarski(X3,k1_wellord1(sK7,X0))
    | X2 != X3 ),
    inference(resolution,[status(thm)],[c_1327,c_518])).

cnf(c_5531,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
    | r1_tarski(X1,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK6))
    | X1 != k1_wellord1(sK7,sK5) ),
    inference(resolution,[status(thm)],[c_5281,c_34])).

cnf(c_15771,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_wellord1(sK7,sK6),X2)
    | X1 != k1_wellord1(sK7,sK5) ),
    inference(resolution,[status(thm)],[c_11587,c_5531])).

cnf(c_18,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_88,plain,
    ( v1_relat_2(sK7)
    | ~ v2_wellord1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_121,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_125,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2480,plain,
    ( r2_hidden(k4_tarski(sK6,sK6),sK7)
    | ~ r2_hidden(sK6,k3_relat_1(sK7))
    | ~ v1_relat_2(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2786,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1330,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_3092,plain,
    ( X0 != sK6
    | X1 != sK6
    | k4_tarski(X0,X1) = k4_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_5660,plain,
    ( X0 != sK6
    | k4_tarski(X0,sK6) = k4_tarski(sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3092])).

cnf(c_8772,plain,
    ( k4_tarski(sK5,sK6) = k4_tarski(sK6,sK6)
    | sK6 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5660])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2119,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10244,plain,
    ( sK6 = sK5
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10237,c_2119])).

cnf(c_10265,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ v1_relat_1(sK7)
    | sK6 = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10244])).

cnf(c_1328,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2561,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
    | X0 != k4_tarski(sK6,sK6)
    | X1 != sK7 ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_3091,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
    | X2 != sK7
    | k4_tarski(X0,X1) != k4_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_14816,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
    | r2_hidden(k4_tarski(sK5,sK6),X0)
    | X0 != sK7
    | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_3091])).

cnf(c_14818,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
    | r2_hidden(k4_tarski(sK5,sK6),sK7)
    | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_14816])).

cnf(c_3002,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_5934,plain,
    ( X0 = sK6
    | X0 != sK5
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_15554,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5934])).

cnf(c_16070,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15771,c_38,c_37,c_35,c_88,c_121,c_125,c_2480,c_2786,c_3317,c_8772,c_10265,c_14818,c_15554])).

cnf(c_16072,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16070])).

cnf(c_16694,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14285,c_16072])).

cnf(c_16699,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),X0) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16694,c_2127])).

cnf(c_17124,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK7,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16699,c_2127])).

cnf(c_17581,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k3_relat_1(X0)) = iProver_top
    | r1_tarski(sK7,k1_wellord1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2107,c_17124])).

cnf(c_18765,plain,
    ( sK6 = sK5
    | r2_hidden(k4_tarski(sK5,sK6),k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)))) = iProver_top
    | r1_tarski(sK7,k1_wellord1(sK7,sK5)) != iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10245,c_17581])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2117,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11174,plain,
    ( sK6 = sK5
    | r2_hidden(X0,k1_wellord1(sK7,sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k2_wellord1(sK7,k1_wellord1(sK7,sK6))) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10245,c_2119])).

cnf(c_44,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2106,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4774,plain,
    ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_2106])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2129,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15951,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_2129])).

cnf(c_2124,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3716,plain,
    ( r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
    | r1_tarski(k3_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2107,c_2124])).

cnf(c_11172,plain,
    ( sK6 = sK5
    | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))),X0) != iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10245,c_3716])).

cnf(c_20244,plain,
    ( sK6 = sK5
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15951,c_11172])).

cnf(c_20986,plain,
    ( sK6 = sK5
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11174,c_39,c_44,c_16072,c_20244])).

cnf(c_20992,plain,
    ( sK6 = sK5
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2117,c_20986])).

cnf(c_20995,plain,
    ( sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18765,c_39,c_20992])).

cnf(c_21019,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20995,c_16694])).

cnf(c_2104,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21052,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20995,c_2104])).

cnf(c_21188,plain,
    ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_21019,c_21052])).

cnf(c_19289,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5))
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19292,plain,
    ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5)) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19289])).

cnf(c_3809,plain,
    ( r2_hidden(sK0(k1_wellord1(sK7,sK5),X0),k1_wellord1(sK7,sK5))
    | r1_tarski(k1_wellord1(sK7,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10361,plain,
    ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)),k1_wellord1(sK7,sK5))
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_3809])).

cnf(c_10364,plain,
    ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)),k1_wellord1(sK7,sK5)) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10361])).

cnf(c_10366,plain,
    ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5)) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10364])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21188,c_19292,c_10366])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.70/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.50  
% 7.70/1.50  ------  iProver source info
% 7.70/1.50  
% 7.70/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.50  git: non_committed_changes: false
% 7.70/1.50  git: last_make_outside_of_git: false
% 7.70/1.50  
% 7.70/1.50  ------ 
% 7.70/1.50  ------ Parsing...
% 7.70/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  ------ Proving...
% 7.70/1.50  ------ Problem Properties 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  clauses                                 33
% 7.70/1.50  conjectures                             5
% 7.70/1.50  EPR                                     7
% 7.70/1.50  Horn                                    23
% 7.70/1.50  unary                                   6
% 7.70/1.50  binary                                  8
% 7.70/1.50  lits                                    89
% 7.70/1.50  lits eq                                 10
% 7.70/1.50  fd_pure                                 0
% 7.70/1.50  fd_pseudo                               0
% 7.70/1.50  fd_cond                                 0
% 7.70/1.50  fd_pseudo_cond                          5
% 7.70/1.50  AC symbols                              0
% 7.70/1.50  
% 7.70/1.50  ------ Input Options Time Limit: Unbounded
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ 
% 7.70/1.50  Current options:
% 7.70/1.50  ------ 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  % SZS status Theorem for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  fof(f12,conjecture,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f13,negated_conjecture,(
% 7.70/1.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.70/1.50    inference(negated_conjecture,[],[f12])).
% 7.70/1.50  
% 7.70/1.50  fof(f27,plain,(
% 7.70/1.50    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 7.70/1.50    inference(ennf_transformation,[],[f13])).
% 7.70/1.50  
% 7.70/1.50  fof(f28,plain,(
% 7.70/1.50    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.70/1.50    inference(flattening,[],[f27])).
% 7.70/1.50  
% 7.70/1.50  fof(f50,plain,(
% 7.70/1.50    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.70/1.50    inference(nnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f51,plain,(
% 7.70/1.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.70/1.50    inference(flattening,[],[f50])).
% 7.70/1.50  
% 7.70/1.50  fof(f52,plain,(
% 7.70/1.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & r2_hidden(sK6,k3_relat_1(sK7)) & r2_hidden(sK5,k3_relat_1(sK7)) & v2_wellord1(sK7) & v1_relat_1(sK7))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f53,plain,(
% 7.70/1.50    (~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & r2_hidden(sK6,k3_relat_1(sK7)) & r2_hidden(sK5,k3_relat_1(sK7)) & v2_wellord1(sK7) & v1_relat_1(sK7)),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f51,f52])).
% 7.70/1.50  
% 7.70/1.50  fof(f91,plain,(
% 7.70/1.50    r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f1,axiom,(
% 7.70/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f14,plain,(
% 7.70/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.70/1.50    inference(ennf_transformation,[],[f1])).
% 7.70/1.50  
% 7.70/1.50  fof(f29,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.70/1.50    inference(nnf_transformation,[],[f14])).
% 7.70/1.50  
% 7.70/1.50  fof(f30,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.70/1.50    inference(rectify,[],[f29])).
% 7.70/1.50  
% 7.70/1.50  fof(f31,plain,(
% 7.70/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f32,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.70/1.50  
% 7.70/1.50  fof(f55,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f32])).
% 7.70/1.50  
% 7.70/1.50  fof(f54,plain,(
% 7.70/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f32])).
% 7.70/1.50  
% 7.70/1.50  fof(f11,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f25,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(ennf_transformation,[],[f11])).
% 7.70/1.50  
% 7.70/1.50  fof(f26,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(flattening,[],[f25])).
% 7.70/1.50  
% 7.70/1.50  fof(f86,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f26])).
% 7.70/1.50  
% 7.70/1.50  fof(f88,plain,(
% 7.70/1.50    v2_wellord1(sK7)),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f87,plain,(
% 7.70/1.50    v1_relat_1(sK7)),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f4,axiom,(
% 7.70/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f17,plain,(
% 7.70/1.50    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f4])).
% 7.70/1.50  
% 7.70/1.50  fof(f35,plain,(
% 7.70/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f17])).
% 7.70/1.50  
% 7.70/1.50  fof(f36,plain,(
% 7.70/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(flattening,[],[f35])).
% 7.70/1.50  
% 7.70/1.50  fof(f37,plain,(
% 7.70/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(rectify,[],[f36])).
% 7.70/1.50  
% 7.70/1.50  fof(f38,plain,(
% 7.70/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f39,plain,(
% 7.70/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.70/1.50  
% 7.70/1.50  fof(f63,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f39])).
% 7.70/1.50  
% 7.70/1.50  fof(f95,plain,(
% 7.70/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f63])).
% 7.70/1.50  
% 7.70/1.50  fof(f61,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f39])).
% 7.70/1.50  
% 7.70/1.50  fof(f97,plain,(
% 7.70/1.50    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f61])).
% 7.70/1.50  
% 7.70/1.50  fof(f98,plain,(
% 7.70/1.50    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f97])).
% 7.70/1.50  
% 7.70/1.50  fof(f8,axiom,(
% 7.70/1.50    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f21,plain,(
% 7.70/1.50    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f8])).
% 7.70/1.50  
% 7.70/1.50  fof(f46,plain,(
% 7.70/1.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f21])).
% 7.70/1.50  
% 7.70/1.50  fof(f47,plain,(
% 7.70/1.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(rectify,[],[f46])).
% 7.70/1.50  
% 7.70/1.50  fof(f48,plain,(
% 7.70/1.50    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0))))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f49,plain,(
% 7.70/1.50    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f48])).
% 7.70/1.50  
% 7.70/1.50  fof(f77,plain,(
% 7.70/1.50    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f49])).
% 7.70/1.50  
% 7.70/1.50  fof(f3,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f15,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.70/1.50    inference(ennf_transformation,[],[f3])).
% 7.70/1.50  
% 7.70/1.50  fof(f16,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.70/1.50    inference(flattening,[],[f15])).
% 7.70/1.50  
% 7.70/1.50  fof(f60,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f16])).
% 7.70/1.50  
% 7.70/1.50  fof(f92,plain,(
% 7.70/1.50    ~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f89,plain,(
% 7.70/1.50    r2_hidden(sK5,k3_relat_1(sK7))),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f90,plain,(
% 7.70/1.50    r2_hidden(sK6,k3_relat_1(sK7))),
% 7.70/1.50    inference(cnf_transformation,[],[f53])).
% 7.70/1.50  
% 7.70/1.50  fof(f5,axiom,(
% 7.70/1.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f18,plain,(
% 7.70/1.50    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f5])).
% 7.70/1.50  
% 7.70/1.50  fof(f40,plain,(
% 7.70/1.50    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f18])).
% 7.70/1.50  
% 7.70/1.50  fof(f41,plain,(
% 7.70/1.50    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(flattening,[],[f40])).
% 7.70/1.50  
% 7.70/1.50  fof(f70,plain,(
% 7.70/1.50    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f41])).
% 7.70/1.50  
% 7.70/1.50  fof(f9,axiom,(
% 7.70/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f22,plain,(
% 7.70/1.50    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.70/1.50    inference(ennf_transformation,[],[f9])).
% 7.70/1.50  
% 7.70/1.50  fof(f83,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f22])).
% 7.70/1.50  
% 7.70/1.50  fof(f67,plain,(
% 7.70/1.50    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f41])).
% 7.70/1.50  
% 7.70/1.50  fof(f2,axiom,(
% 7.70/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f33,plain,(
% 7.70/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.70/1.50    inference(nnf_transformation,[],[f2])).
% 7.70/1.50  
% 7.70/1.50  fof(f34,plain,(
% 7.70/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.70/1.50    inference(flattening,[],[f33])).
% 7.70/1.50  
% 7.70/1.50  fof(f57,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.70/1.50    inference(cnf_transformation,[],[f34])).
% 7.70/1.50  
% 7.70/1.50  fof(f94,plain,(
% 7.70/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.70/1.50    inference(equality_resolution,[],[f57])).
% 7.70/1.50  
% 7.70/1.50  fof(f59,plain,(
% 7.70/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f34])).
% 7.70/1.50  
% 7.70/1.50  fof(f7,axiom,(
% 7.70/1.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f20,plain,(
% 7.70/1.50    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f7])).
% 7.70/1.50  
% 7.70/1.50  fof(f42,plain,(
% 7.70/1.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f20])).
% 7.70/1.50  
% 7.70/1.50  fof(f43,plain,(
% 7.70/1.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(rectify,[],[f42])).
% 7.70/1.50  
% 7.70/1.50  fof(f44,plain,(
% 7.70/1.50    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f45,plain,(
% 7.70/1.50    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 7.70/1.50  
% 7.70/1.50  fof(f74,plain,(
% 7.70/1.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f45])).
% 7.70/1.50  
% 7.70/1.50  fof(f62,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f39])).
% 7.70/1.50  
% 7.70/1.50  fof(f96,plain,(
% 7.70/1.50    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f62])).
% 7.70/1.50  
% 7.70/1.50  fof(f6,axiom,(
% 7.70/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f19,plain,(
% 7.70/1.50    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f6])).
% 7.70/1.50  
% 7.70/1.50  fof(f73,plain,(
% 7.70/1.50    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f19])).
% 7.70/1.50  
% 7.70/1.50  fof(f10,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f23,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(ennf_transformation,[],[f10])).
% 7.70/1.50  
% 7.70/1.50  fof(f24,plain,(
% 7.70/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(flattening,[],[f23])).
% 7.70/1.50  
% 7.70/1.50  fof(f85,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f24])).
% 7.70/1.50  
% 7.70/1.50  fof(f56,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f32])).
% 7.70/1.50  
% 7.70/1.50  cnf(c_34,negated_conjecture,
% 7.70/1.50      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.50      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2103,plain,
% 7.70/1.50      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.50      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1,plain,
% 7.70/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2128,plain,
% 7.70/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.70/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.70/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2127,plain,
% 7.70/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.70/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.70/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4982,plain,
% 7.70/1.50      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.70/1.50      | r1_tarski(X0,X2) != iProver_top
% 7.70/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2128,c_2127]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_32,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.70/1.50      | ~ v2_wellord1(X1)
% 7.70/1.50      | ~ v1_relat_1(X1)
% 7.70/1.50      | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0) ),
% 7.70/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_37,negated_conjecture,
% 7.70/1.50      ( v2_wellord1(sK7) ),
% 7.70/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_514,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.70/1.50      | ~ v1_relat_1(X1)
% 7.70/1.50      | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0)
% 7.70/1.50      | sK7 != X1 ),
% 7.70/1.50      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_515,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.70/1.50      | ~ v1_relat_1(sK7)
% 7.70/1.50      | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
% 7.70/1.50      inference(unflattening,[status(thm)],[c_514]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_38,negated_conjecture,
% 7.70/1.50      ( v1_relat_1(sK7) ),
% 7.70/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_518,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.70/1.50      | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_515,c_38]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2097,plain,
% 7.70/1.50      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),X1) = k1_wellord1(sK7,X1)
% 7.70/1.50      | r2_hidden(X1,k1_wellord1(sK7,X0)) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_8551,plain,
% 7.70/1.50      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(X1,X2)) = k1_wellord1(sK7,sK0(X1,X2))
% 7.70/1.50      | r1_tarski(X1,X2) = iProver_top
% 7.70/1.50      | r1_tarski(X1,k1_wellord1(sK7,X0)) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_4982,c_2097]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_9275,plain,
% 7.70/1.50      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),X0)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))
% 7.70/1.50      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.50      | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2103,c_8551]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_10,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.70/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.70/1.50      | ~ v1_relat_1(X1)
% 7.70/1.50      | X0 = X2 ),
% 7.70/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2120,plain,
% 7.70/1.50      ( X0 = X1
% 7.70/1.50      | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
% 7.70/1.50      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 7.70/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_9533,plain,
% 7.70/1.50      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),X0)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))
% 7.70/1.50      | sK6 = sK5
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
% 7.70/1.50      | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
% 7.70/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_9275,c_2120]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_39,plain,
% 7.70/1.50      ( v1_relat_1(sK7) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1325,plain,( X0 = X0 ),theory(equality) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3317,plain,
% 7.70/1.50      ( sK6 = sK6 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1325]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2791,plain,
% 7.70/1.50      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1326]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3698,plain,
% 7.70/1.50      ( X0 != sK6 | X0 = sK5 | sK5 != sK6 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_2791]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6324,plain,
% 7.70/1.50      ( sK6 != sK6 | sK6 = sK5 | sK5 != sK6 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_3698]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2881,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(k4_tarski(sK5,sK6),sK7) ),
% 7.70/1.50      inference(resolution,[status(thm)],[c_2,c_34]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6930,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ v1_relat_1(sK7)
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(resolution,[status(thm)],[c_10,c_2881]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7187,plain,
% 7.70/1.50      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(X0,k1_wellord1(sK7,sK6))
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_6930,c_38]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7188,plain,
% 7.70/1.50      ( r2_hidden(X0,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ r2_hidden(X0,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_7187]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_12,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7475,plain,
% 7.70/1.50      ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ v1_relat_1(sK7)
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(resolution,[status(thm)],[c_7188,c_12]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_8424,plain,
% 7.70/1.50      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_7475,c_38]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_8425,plain,
% 7.70/1.50      ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.50      | sK5 = sK6 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_8424]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_8426,plain,
% 7.70/1.50      ( sK5 = sK6
% 7.70/1.50      | r2_hidden(sK6,k1_wellord1(sK7,sK5)) != iProver_top
% 7.70/1.50      | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_8425]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_28,plain,
% 7.70/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.70/1.51      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.70/1.51      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.70/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.70/1.51      | ~ v6_relat_2(X1)
% 7.70/1.51      | ~ v1_relat_1(X1)
% 7.70/1.51      | X0 = X2 ),
% 7.70/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_6,plain,
% 7.70/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.70/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3182,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | r1_tarski(X0,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r1_tarski(X0,k1_wellord1(sK7,sK5)) ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_6,c_34]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_6931,plain,
% 7.70/1.51      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | r1_tarski(X0,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
% 7.70/1.51      | ~ v1_relat_1(sK7)
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_10,c_3182]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_7486,plain,
% 7.70/1.51      ( ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
% 7.70/1.51      | r1_tarski(X0,k1_wellord1(sK7,sK6))
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_6931,c_38]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_7487,plain,
% 7.70/1.51      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | r1_tarski(X0,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r1_tarski(X0,k1_wellord1(sK7,sK5))
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(renaming,[status(thm)],[c_7486]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_33,negated_conjecture,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
% 7.70/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_7518,plain,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5))
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_7487,c_33]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2506,plain,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ v1_relat_1(sK7)
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_7760,plain,
% 7.70/1.51      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_7518,c_38,c_2506]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_7761,plain,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(renaming,[status(thm)],[c_7760]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_9072,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK6,sK5),sK7)
% 7.70/1.51      | ~ r2_hidden(sK6,k3_relat_1(sK7))
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ r2_hidden(sK5,k3_relat_1(sK7))
% 7.70/1.51      | ~ v6_relat_2(sK7)
% 7.70/1.51      | ~ v1_relat_1(sK7)
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_28,c_7761]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_36,negated_conjecture,
% 7.70/1.51      ( r2_hidden(sK5,k3_relat_1(sK7)) ),
% 7.70/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_35,negated_conjecture,
% 7.70/1.51      ( r2_hidden(sK6,k3_relat_1(sK7)) ),
% 7.70/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_15,plain,
% 7.70/1.51      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.70/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_97,plain,
% 7.70/1.51      ( v6_relat_2(sK7) | ~ v2_wellord1(sK7) | ~ v1_relat_1(sK7) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_9404,plain,
% 7.70/1.51      ( r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | r2_hidden(k4_tarski(sK6,sK5),sK7)
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_9072,c_38,c_37,c_36,c_35,c_97]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_9405,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK6,sK5),sK7)
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(renaming,[status(thm)],[c_9404]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_9636,plain,
% 7.70/1.51      ( r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6))
% 7.70/1.51      | ~ v1_relat_1(sK7)
% 7.70/1.51      | sK6 = sK5
% 7.70/1.51      | sK5 = sK6 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_9405,c_10]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_9637,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | sK5 = sK6
% 7.70/1.51      | r2_hidden(sK6,k1_wellord1(sK7,sK5)) = iProver_top
% 7.70/1.51      | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
% 7.70/1.51      | v1_relat_1(sK7) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_9636]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10237,plain,
% 7.70/1.51      ( sK6 = sK5 | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_9533,c_39,c_3317,c_6324,c_8426,c_9637]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10245,plain,
% 7.70/1.51      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK5) = k1_wellord1(sK7,sK5)
% 7.70/1.51      | sK6 = sK5 ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_10237,c_2097]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_29,plain,
% 7.70/1.51      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.70/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2107,plain,
% 7.70/1.51      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2100,plain,
% 7.70/1.51      ( v1_relat_1(sK7) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2118,plain,
% 7.70/1.51      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 7.70/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_8548,plain,
% 7.70/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.70/1.51      | r1_tarski(X0,k1_wellord1(X2,sK0(X0,X1))) != iProver_top
% 7.70/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_4982,c_2118]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_13022,plain,
% 7.70/1.51      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1)))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1))))
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),X1) = iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_9275,c_8548]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_14250,plain,
% 7.70/1.51      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0)))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),X0))))
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_2100,c_13022]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_14285,plain,
% 7.70/1.51      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1)))))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK0(k1_wellord1(sK7,sK5),X1))))))
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),X1) = iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_14250,c_8548]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_1327,plain,
% 7.70/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.70/1.51      theory(equality) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5277,plain,
% 7.70/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_1327,c_1325]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10814,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.70/1.51      | r1_tarski(k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0),X2)
% 7.70/1.51      | ~ r1_tarski(k1_wellord1(sK7,X0),X2) ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_5277,c_518]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_11587,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.70/1.51      | r1_tarski(X2,X3)
% 7.70/1.51      | ~ r1_tarski(X2,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0))
% 7.70/1.51      | ~ r1_tarski(k1_wellord1(sK7,X0),X3) ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_10814,c_6]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5281,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.70/1.51      | r1_tarski(X2,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0))
% 7.70/1.51      | ~ r1_tarski(X3,k1_wellord1(sK7,X0))
% 7.70/1.51      | X2 != X3 ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_1327,c_518]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5531,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
% 7.70/1.51      | r1_tarski(X1,k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK6))
% 7.70/1.51      | X1 != k1_wellord1(sK7,sK5) ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_5281,c_34]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_15771,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
% 7.70/1.51      | r1_tarski(X1,X2)
% 7.70/1.51      | ~ r1_tarski(k1_wellord1(sK7,sK6),X2)
% 7.70/1.51      | X1 != k1_wellord1(sK7,sK5) ),
% 7.70/1.51      inference(resolution,[status(thm)],[c_11587,c_5531]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_18,plain,
% 7.70/1.51      ( v1_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.70/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_88,plain,
% 7.70/1.51      ( v1_relat_2(sK7) | ~ v2_wellord1(sK7) | ~ v1_relat_1(sK7) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5,plain,
% 7.70/1.51      ( r1_tarski(X0,X0) ),
% 7.70/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_121,plain,
% 7.70/1.51      ( r1_tarski(sK7,sK7) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3,plain,
% 7.70/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.70/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_125,plain,
% 7.70/1.51      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_22,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.70/1.51      | r2_hidden(k4_tarski(X0,X0),X1)
% 7.70/1.51      | ~ v1_relat_2(X1)
% 7.70/1.51      | ~ v1_relat_1(X1) ),
% 7.70/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2480,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.70/1.51      | ~ r2_hidden(sK6,k3_relat_1(sK7))
% 7.70/1.51      | ~ v1_relat_2(sK7)
% 7.70/1.51      | ~ v1_relat_1(sK7) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2786,plain,
% 7.70/1.51      ( sK5 = sK5 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_1325]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_1330,plain,
% 7.70/1.51      ( X0 != X1 | X2 != X3 | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
% 7.70/1.51      theory(equality) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3092,plain,
% 7.70/1.51      ( X0 != sK6 | X1 != sK6 | k4_tarski(X0,X1) = k4_tarski(sK6,sK6) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_1330]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5660,plain,
% 7.70/1.51      ( X0 != sK6 | k4_tarski(X0,sK6) = k4_tarski(sK6,sK6) | sK6 != sK6 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_3092]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_8772,plain,
% 7.70/1.51      ( k4_tarski(sK5,sK6) = k4_tarski(sK6,sK6)
% 7.70/1.51      | sK6 != sK6
% 7.70/1.51      | sK5 != sK6 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_5660]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_11,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.70/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.70/1.51      | ~ v1_relat_1(X1) ),
% 7.70/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2119,plain,
% 7.70/1.51      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 7.70/1.51      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 7.70/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10244,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.70/1.51      | v1_relat_1(sK7) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_10237,c_2119]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10265,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | ~ v1_relat_1(sK7)
% 7.70/1.51      | sK6 = sK5 ),
% 7.70/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_10244]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_1328,plain,
% 7.70/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.70/1.51      theory(equality) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2561,plain,
% 7.70/1.51      ( r2_hidden(X0,X1)
% 7.70/1.51      | ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.70/1.51      | X0 != k4_tarski(sK6,sK6)
% 7.70/1.51      | X1 != sK7 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_1328]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3091,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(X0,X1),X2)
% 7.70/1.51      | ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.70/1.51      | X2 != sK7
% 7.70/1.51      | k4_tarski(X0,X1) != k4_tarski(sK6,sK6) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_2561]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_14816,plain,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),X0)
% 7.70/1.51      | X0 != sK7
% 7.70/1.51      | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_3091]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_14818,plain,
% 7.70/1.51      ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.70/1.51      | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
% 7.70/1.51      | sK7 != sK7 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_14816]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3002,plain,
% 7.70/1.51      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_1326]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_5934,plain,
% 7.70/1.51      ( X0 = sK6 | X0 != sK5 | sK6 != sK5 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_3002]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_15554,plain,
% 7.70/1.51      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_5934]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_16070,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7) ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_15771,c_38,c_37,c_35,c_88,c_121,c_125,c_2480,c_2786,
% 7.70/1.51                 c_3317,c_8772,c_10265,c_14818,c_15554]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_16072,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_16070]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_16694,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_14285,c_16072]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_16699,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),X0) = iProver_top
% 7.70/1.51      | r1_tarski(sK7,X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_16694,c_2127]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_17124,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),X0) = iProver_top
% 7.70/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.70/1.51      | r1_tarski(sK7,X1) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_16699,c_2127]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_17581,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),k3_relat_1(X0)) = iProver_top
% 7.70/1.51      | r1_tarski(sK7,k1_wellord1(X0,X1)) != iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_2107,c_17124]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_18765,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | r2_hidden(k4_tarski(sK5,sK6),k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)))) = iProver_top
% 7.70/1.51      | r1_tarski(sK7,k1_wellord1(sK7,sK5)) != iProver_top
% 7.70/1.51      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_10245,c_17581]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_19,plain,
% 7.70/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 7.70/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2117,plain,
% 7.70/1.51      ( v1_relat_1(X0) != iProver_top
% 7.70/1.51      | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_11174,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | r2_hidden(X0,k1_wellord1(sK7,sK5)) != iProver_top
% 7.70/1.51      | r2_hidden(k4_tarski(X0,sK5),k2_wellord1(sK7,k1_wellord1(sK7,sK6))) = iProver_top
% 7.70/1.51      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_10245,c_2119]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_44,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_30,plain,
% 7.70/1.51      ( r2_hidden(X0,X1)
% 7.70/1.51      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
% 7.70/1.51      | ~ v1_relat_1(X2) ),
% 7.70/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2106,plain,
% 7.70/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.70/1.51      | r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) != iProver_top
% 7.70/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_4774,plain,
% 7.70/1.51      ( r2_hidden(sK0(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) = iProver_top
% 7.70/1.51      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) = iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_2128,c_2106]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_0,plain,
% 7.70/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.70/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2129,plain,
% 7.70/1.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.70/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_15951,plain,
% 7.70/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) = iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_4774,c_2129]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2124,plain,
% 7.70/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.70/1.51      | r1_tarski(X1,X2) != iProver_top
% 7.70/1.51      | r1_tarski(X0,X2) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3716,plain,
% 7.70/1.51      ( r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
% 7.70/1.51      | r1_tarski(k3_relat_1(X0),X2) != iProver_top
% 7.70/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_2107,c_2124]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_11172,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
% 7.70/1.51      | r1_tarski(k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))),X0) != iProver_top
% 7.70/1.51      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_10245,c_3716]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_20244,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top
% 7.70/1.51      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
% 7.70/1.51      | v1_relat_1(sK7) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_15951,c_11172]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_20986,plain,
% 7.70/1.51      ( sK6 = sK5
% 7.70/1.51      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_11174,c_39,c_44,c_16072,c_20244]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_20992,plain,
% 7.70/1.51      ( sK6 = sK5 | v1_relat_1(sK7) != iProver_top ),
% 7.70/1.51      inference(superposition,[status(thm)],[c_2117,c_20986]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_20995,plain,
% 7.70/1.51      ( sK6 = sK5 ),
% 7.70/1.51      inference(global_propositional_subsumption,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_18765,c_39,c_20992]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_21019,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK5),sK7) = iProver_top ),
% 7.70/1.51      inference(demodulation,[status(thm)],[c_20995,c_16694]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_2104,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_21052,plain,
% 7.70/1.51      ( r2_hidden(k4_tarski(sK5,sK5),sK7) != iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
% 7.70/1.51      inference(demodulation,[status(thm)],[c_20995,c_2104]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_21188,plain,
% 7.70/1.51      ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
% 7.70/1.51      inference(backward_subsumption_resolution,
% 7.70/1.51                [status(thm)],
% 7.70/1.51                [c_21019,c_21052]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_19289,plain,
% 7.70/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5))
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_19292,plain,
% 7.70/1.51      ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5)) != iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_19289]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_3809,plain,
% 7.70/1.51      ( r2_hidden(sK0(k1_wellord1(sK7,sK5),X0),k1_wellord1(sK7,sK5))
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),X0) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10361,plain,
% 7.70/1.51      ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)),k1_wellord1(sK7,sK5))
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)) ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_3809]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10364,plain,
% 7.70/1.51      ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)),k1_wellord1(sK7,sK5)) = iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(X0,sK5)) = iProver_top ),
% 7.70/1.51      inference(predicate_to_equality,[status(thm)],[c_10361]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(c_10366,plain,
% 7.70/1.51      ( r2_hidden(sK0(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)),k1_wellord1(sK7,sK5)) = iProver_top
% 7.70/1.51      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) = iProver_top ),
% 7.70/1.51      inference(instantiation,[status(thm)],[c_10364]) ).
% 7.70/1.51  
% 7.70/1.51  cnf(contradiction,plain,
% 7.70/1.51      ( $false ),
% 7.70/1.51      inference(minisat,[status(thm)],[c_21188,c_19292,c_10366]) ).
% 7.70/1.51  
% 7.70/1.51  
% 7.70/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.51  
% 7.70/1.51  ------                               Statistics
% 7.70/1.51  
% 7.70/1.51  ------ Selected
% 7.70/1.51  
% 7.70/1.51  total_time:                             0.594
% 7.70/1.51  
%------------------------------------------------------------------------------
