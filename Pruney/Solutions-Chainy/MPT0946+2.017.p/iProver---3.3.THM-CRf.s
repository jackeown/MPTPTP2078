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
% DateTime   : Thu Dec  3 11:59:44 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 787 expanded)
%              Number of clauses        :   80 ( 267 expanded)
%              Number of leaves         :   19 ( 169 expanded)
%              Depth                    :   26
%              Number of atoms          :  583 (3485 expanded)
%              Number of equality atoms :  211 (1077 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK5 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK5))
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( sK4 != sK5
    & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f47,f46])).

fof(f74,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f48])).

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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f19])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f81,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f76,plain,(
    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f63])).

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

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1677,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1678,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1696,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1681,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3118,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1696,c_1681])).

cnf(c_8984,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_1681])).

cnf(c_9227,plain,
    ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | k1_wellord1(k1_wellord2(sK5),X0) = X0
    | sK5 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_8984])).

cnf(c_9255,plain,
    ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1677,c_9227])).

cnf(c_25,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1211,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1238,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1212,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1955,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1956,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_9429,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | k1_wellord1(k1_wellord2(sK5),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9255,c_25,c_1238,c_1956])).

cnf(c_9430,plain,
    ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(renaming,[status(thm)],[c_9429])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1690,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9438,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r2_hidden(sK4,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9430,c_1690])).

cnf(c_26,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_21,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2147,plain,
    ( r2_hidden(sK5,sK4)
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2280,plain,
    ( ~ r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5)
    | k1_wellord1(k1_wellord2(X0),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2283,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_12,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1940,plain,
    ( ~ r4_wellord1(X0,k1_wellord2(X1))
    | r4_wellord1(k1_wellord2(X1),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2126,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_2661,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_2774,plain,
    ( v1_relat_1(k1_wellord2(sK5)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_163,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1700,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1691,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2804,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(X0,X1),X2),X1),X0) = iProver_top
    | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1691])).

cnf(c_4,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1697,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4105,plain,
    ( r2_hidden(sK0(k1_wellord1(X0,X1),X2),k3_relat_1(X0)) = iProver_top
    | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_1697])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1701,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4844,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_1701])).

cnf(c_4984,plain,
    ( r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_163,c_4844])).

cnf(c_41,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5001,plain,
    ( r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4984,c_41])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1680,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5008,plain,
    ( k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)) = k1_wellord2(k1_wellord1(k1_wellord2(X0),X1)) ),
    inference(superposition,[status(thm)],[c_5001,c_1680])).

cnf(c_13,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_315,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v3_ordinal1(X2)
    | ~ v1_relat_1(X0)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_316,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_320,plain,
    ( ~ v3_ordinal1(X0)
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_21])).

cnf(c_321,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_1676,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_1800,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1676,c_163])).

cnf(c_5094,plain,
    ( r4_wellord1(k1_wellord2(X0),k1_wellord2(k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5008,c_1800])).

cnf(c_9445,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9430,c_5094])).

cnf(c_9581,plain,
    ( ~ r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9445])).

cnf(c_9821,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9438,c_28,c_27,c_26,c_25,c_42,c_2147,c_2283,c_2661,c_2774,c_9581])).

cnf(c_9827,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9821,c_1691])).

cnf(c_43,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_10142,plain,
    ( r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9827,c_43])).

cnf(c_10143,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10142])).

cnf(c_3,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1698,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10151,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10143,c_1698])).

cnf(c_10199,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10151,c_163])).

cnf(c_10225,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10199])).

cnf(c_9836,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9821,c_5094])).

cnf(c_2148,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_31,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10225,c_9836,c_2148,c_43,c_25,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.00  
% 3.33/1.00  ------  iProver source info
% 3.33/1.00  
% 3.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.00  git: non_committed_changes: false
% 3.33/1.00  git: last_make_outside_of_git: false
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     num_symb
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       true
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  ------ Parsing...
% 3.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.00  ------ Proving...
% 3.33/1.00  ------ Problem Properties 
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  clauses                                 28
% 3.33/1.00  conjectures                             4
% 3.33/1.00  EPR                                     6
% 3.33/1.00  Horn                                    19
% 3.33/1.00  unary                                   6
% 3.33/1.00  binary                                  4
% 3.33/1.00  lits                                    83
% 3.33/1.00  lits eq                                 15
% 3.33/1.00  fd_pure                                 0
% 3.33/1.00  fd_pseudo                               0
% 3.33/1.00  fd_cond                                 0
% 3.33/1.00  fd_pseudo_cond                          4
% 3.33/1.00  AC symbols                              0
% 3.33/1.00  
% 3.33/1.00  ------ Schedule dynamic 5 is on 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ 
% 3.33/1.00  Current options:
% 3.33/1.00  ------ 
% 3.33/1.00  
% 3.33/1.00  ------ Input Options
% 3.33/1.00  
% 3.33/1.00  --out_options                           all
% 3.33/1.00  --tptp_safe_out                         true
% 3.33/1.00  --problem_path                          ""
% 3.33/1.00  --include_path                          ""
% 3.33/1.00  --clausifier                            res/vclausify_rel
% 3.33/1.00  --clausifier_options                    --mode clausify
% 3.33/1.00  --stdin                                 false
% 3.33/1.00  --stats_out                             all
% 3.33/1.00  
% 3.33/1.00  ------ General Options
% 3.33/1.00  
% 3.33/1.00  --fof                                   false
% 3.33/1.00  --time_out_real                         305.
% 3.33/1.00  --time_out_virtual                      -1.
% 3.33/1.00  --symbol_type_check                     false
% 3.33/1.00  --clausify_out                          false
% 3.33/1.00  --sig_cnt_out                           false
% 3.33/1.00  --trig_cnt_out                          false
% 3.33/1.00  --trig_cnt_out_tolerance                1.
% 3.33/1.00  --trig_cnt_out_sk_spl                   false
% 3.33/1.00  --abstr_cl_out                          false
% 3.33/1.00  
% 3.33/1.00  ------ Global Options
% 3.33/1.00  
% 3.33/1.00  --schedule                              default
% 3.33/1.00  --add_important_lit                     false
% 3.33/1.00  --prop_solver_per_cl                    1000
% 3.33/1.00  --min_unsat_core                        false
% 3.33/1.00  --soft_assumptions                      false
% 3.33/1.00  --soft_lemma_size                       3
% 3.33/1.00  --prop_impl_unit_size                   0
% 3.33/1.00  --prop_impl_unit                        []
% 3.33/1.00  --share_sel_clauses                     true
% 3.33/1.00  --reset_solvers                         false
% 3.33/1.00  --bc_imp_inh                            [conj_cone]
% 3.33/1.00  --conj_cone_tolerance                   3.
% 3.33/1.00  --extra_neg_conj                        none
% 3.33/1.00  --large_theory_mode                     true
% 3.33/1.00  --prolific_symb_bound                   200
% 3.33/1.00  --lt_threshold                          2000
% 3.33/1.00  --clause_weak_htbl                      true
% 3.33/1.00  --gc_record_bc_elim                     false
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing Options
% 3.33/1.00  
% 3.33/1.00  --preprocessing_flag                    true
% 3.33/1.00  --time_out_prep_mult                    0.1
% 3.33/1.00  --splitting_mode                        input
% 3.33/1.00  --splitting_grd                         true
% 3.33/1.00  --splitting_cvd                         false
% 3.33/1.00  --splitting_cvd_svl                     false
% 3.33/1.00  --splitting_nvd                         32
% 3.33/1.00  --sub_typing                            true
% 3.33/1.00  --prep_gs_sim                           true
% 3.33/1.00  --prep_unflatten                        true
% 3.33/1.00  --prep_res_sim                          true
% 3.33/1.00  --prep_upred                            true
% 3.33/1.00  --prep_sem_filter                       exhaustive
% 3.33/1.00  --prep_sem_filter_out                   false
% 3.33/1.00  --pred_elim                             true
% 3.33/1.00  --res_sim_input                         true
% 3.33/1.00  --eq_ax_congr_red                       true
% 3.33/1.00  --pure_diseq_elim                       true
% 3.33/1.00  --brand_transform                       false
% 3.33/1.00  --non_eq_to_eq                          false
% 3.33/1.00  --prep_def_merge                        true
% 3.33/1.00  --prep_def_merge_prop_impl              false
% 3.33/1.00  --prep_def_merge_mbd                    true
% 3.33/1.00  --prep_def_merge_tr_red                 false
% 3.33/1.00  --prep_def_merge_tr_cl                  false
% 3.33/1.00  --smt_preprocessing                     true
% 3.33/1.00  --smt_ac_axioms                         fast
% 3.33/1.00  --preprocessed_out                      false
% 3.33/1.00  --preprocessed_stats                    false
% 3.33/1.00  
% 3.33/1.00  ------ Abstraction refinement Options
% 3.33/1.00  
% 3.33/1.00  --abstr_ref                             []
% 3.33/1.00  --abstr_ref_prep                        false
% 3.33/1.00  --abstr_ref_until_sat                   false
% 3.33/1.00  --abstr_ref_sig_restrict                funpre
% 3.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.00  --abstr_ref_under                       []
% 3.33/1.00  
% 3.33/1.00  ------ SAT Options
% 3.33/1.00  
% 3.33/1.00  --sat_mode                              false
% 3.33/1.00  --sat_fm_restart_options                ""
% 3.33/1.00  --sat_gr_def                            false
% 3.33/1.00  --sat_epr_types                         true
% 3.33/1.00  --sat_non_cyclic_types                  false
% 3.33/1.00  --sat_finite_models                     false
% 3.33/1.00  --sat_fm_lemmas                         false
% 3.33/1.00  --sat_fm_prep                           false
% 3.33/1.00  --sat_fm_uc_incr                        true
% 3.33/1.00  --sat_out_model                         small
% 3.33/1.00  --sat_out_clauses                       false
% 3.33/1.00  
% 3.33/1.00  ------ QBF Options
% 3.33/1.00  
% 3.33/1.00  --qbf_mode                              false
% 3.33/1.00  --qbf_elim_univ                         false
% 3.33/1.00  --qbf_dom_inst                          none
% 3.33/1.00  --qbf_dom_pre_inst                      false
% 3.33/1.00  --qbf_sk_in                             false
% 3.33/1.00  --qbf_pred_elim                         true
% 3.33/1.00  --qbf_split                             512
% 3.33/1.00  
% 3.33/1.00  ------ BMC1 Options
% 3.33/1.00  
% 3.33/1.00  --bmc1_incremental                      false
% 3.33/1.00  --bmc1_axioms                           reachable_all
% 3.33/1.00  --bmc1_min_bound                        0
% 3.33/1.00  --bmc1_max_bound                        -1
% 3.33/1.00  --bmc1_max_bound_default                -1
% 3.33/1.00  --bmc1_symbol_reachability              true
% 3.33/1.00  --bmc1_property_lemmas                  false
% 3.33/1.00  --bmc1_k_induction                      false
% 3.33/1.00  --bmc1_non_equiv_states                 false
% 3.33/1.00  --bmc1_deadlock                         false
% 3.33/1.00  --bmc1_ucm                              false
% 3.33/1.00  --bmc1_add_unsat_core                   none
% 3.33/1.00  --bmc1_unsat_core_children              false
% 3.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.00  --bmc1_out_stat                         full
% 3.33/1.00  --bmc1_ground_init                      false
% 3.33/1.00  --bmc1_pre_inst_next_state              false
% 3.33/1.00  --bmc1_pre_inst_state                   false
% 3.33/1.00  --bmc1_pre_inst_reach_state             false
% 3.33/1.00  --bmc1_out_unsat_core                   false
% 3.33/1.00  --bmc1_aig_witness_out                  false
% 3.33/1.00  --bmc1_verbose                          false
% 3.33/1.00  --bmc1_dump_clauses_tptp                false
% 3.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.00  --bmc1_dump_file                        -
% 3.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.00  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     none
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       false
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f12,conjecture,(
% 3.33/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f13,negated_conjecture,(
% 3.33/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.33/1.00    inference(negated_conjecture,[],[f12])).
% 3.33/1.00  
% 3.33/1.00  fof(f30,plain,(
% 3.33/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f31,plain,(
% 3.33/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.33/1.00    inference(flattening,[],[f30])).
% 3.33/1.00  
% 3.33/1.00  fof(f47,plain,(
% 3.33/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK5 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK5)) & v3_ordinal1(sK5))) )),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f46,plain,(
% 3.33/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK4 != X1 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f48,plain,(
% 3.33/1.00    (sK4 != sK5 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f47,f46])).
% 3.33/1.00  
% 3.33/1.00  fof(f74,plain,(
% 3.33/1.00    v3_ordinal1(sK4)),
% 3.33/1.00    inference(cnf_transformation,[],[f48])).
% 3.33/1.00  
% 3.33/1.00  fof(f75,plain,(
% 3.33/1.00    v3_ordinal1(sK5)),
% 3.33/1.00    inference(cnf_transformation,[],[f48])).
% 3.33/1.00  
% 3.33/1.00  fof(f3,axiom,(
% 3.33/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f17,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f3])).
% 3.33/1.00  
% 3.33/1.00  fof(f18,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.33/1.00    inference(flattening,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f54,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f18])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f26,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.33/1.00    inference(flattening,[],[f26])).
% 3.33/1.00  
% 3.33/1.00  fof(f71,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f27])).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    sK4 != sK5),
% 3.33/1.00    inference(cnf_transformation,[],[f48])).
% 3.33/1.00  
% 3.33/1.00  fof(f4,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f19,plain,(
% 3.33/1.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f4])).
% 3.33/1.00  
% 3.33/1.00  fof(f36,plain,(
% 3.33/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(nnf_transformation,[],[f19])).
% 3.33/1.00  
% 3.33/1.00  fof(f37,plain,(
% 3.33/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f36])).
% 3.33/1.00  
% 3.33/1.00  fof(f38,plain,(
% 3.33/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(rectify,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f39,plain,(
% 3.33/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f40,plain,(
% 3.33/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.33/1.00  
% 3.33/1.00  fof(f55,plain,(
% 3.33/1.00    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f80,plain,(
% 3.33/1.00    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(equality_resolution,[],[f55])).
% 3.33/1.00  
% 3.33/1.00  fof(f81,plain,(
% 3.33/1.00    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(equality_resolution,[],[f80])).
% 3.33/1.00  
% 3.33/1.00  fof(f76,plain,(
% 3.33/1.00    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))),
% 3.33/1.00    inference(cnf_transformation,[],[f48])).
% 3.33/1.00  
% 3.33/1.00  fof(f8,axiom,(
% 3.33/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f70,plain,(
% 3.33/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f8])).
% 3.33/1.00  
% 3.33/1.00  fof(f5,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f20,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f5])).
% 3.33/1.00  
% 3.33/1.00  fof(f21,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f61,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f21])).
% 3.33/1.00  
% 3.33/1.00  fof(f7,axiom,(
% 3.33/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(ennf_transformation,[],[f7])).
% 3.33/1.00  
% 3.33/1.00  fof(f25,plain,(
% 3.33/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f41,plain,(
% 3.33/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f25])).
% 3.33/1.00  
% 3.33/1.00  fof(f42,plain,(
% 3.33/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(flattening,[],[f41])).
% 3.33/1.00  
% 3.33/1.00  fof(f43,plain,(
% 3.33/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(rectify,[],[f42])).
% 3.33/1.00  
% 3.33/1.00  fof(f44,plain,(
% 3.33/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f45,plain,(
% 3.33/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).
% 3.33/1.00  
% 3.33/1.00  fof(f63,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f45])).
% 3.33/1.00  
% 3.33/1.00  fof(f88,plain,(
% 3.33/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.33/1.00    inference(equality_resolution,[],[f63])).
% 3.33/1.00  
% 3.33/1.00  fof(f1,axiom,(
% 3.33/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f14,plain,(
% 3.33/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.33/1.00    inference(ennf_transformation,[],[f1])).
% 3.33/1.00  
% 3.33/1.00  fof(f32,plain,(
% 3.33/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.00    inference(nnf_transformation,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.00    inference(rectify,[],[f32])).
% 3.33/1.00  
% 3.33/1.00  fof(f34,plain,(
% 3.33/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f35,plain,(
% 3.33/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f50,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f35])).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f79,plain,(
% 3.33/1.00    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(equality_resolution,[],[f56])).
% 3.33/1.00  
% 3.33/1.00  fof(f2,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f15,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(ennf_transformation,[],[f2])).
% 3.33/1.00  
% 3.33/1.00  fof(f16,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(flattening,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f52,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f35])).
% 3.33/1.00  
% 3.33/1.00  fof(f11,axiom,(
% 3.33/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f29,plain,(
% 3.33/1.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.33/1.00    inference(ennf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f29])).
% 3.33/1.00  
% 3.33/1.00  fof(f6,axiom,(
% 3.33/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f22,plain,(
% 3.33/1.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f6])).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f62,plain,(
% 3.33/1.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f23])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,axiom,(
% 3.33/1.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f72,plain,(
% 3.33/1.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f28])).
% 3.33/1.00  
% 3.33/1.00  fof(f53,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_28,negated_conjecture,
% 3.33/1.00      ( v3_ordinal1(sK4) ),
% 3.33/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1677,plain,
% 3.33/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_27,negated_conjecture,
% 3.33/1.00      ( v3_ordinal1(sK5) ),
% 3.33/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1678,plain,
% 3.33/1.00      ( v3_ordinal1(sK5) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5,plain,
% 3.33/1.00      ( r2_hidden(X0,X1)
% 3.33/1.00      | r2_hidden(X1,X0)
% 3.33/1.00      | ~ v3_ordinal1(X1)
% 3.33/1.00      | ~ v3_ordinal1(X0)
% 3.33/1.00      | X1 = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1696,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.33/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.33/1.00      | v3_ordinal1(X1) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_22,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,X1)
% 3.33/1.00      | ~ v3_ordinal1(X1)
% 3.33/1.00      | ~ v3_ordinal1(X0)
% 3.33/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1681,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.33/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.33/1.00      | v3_ordinal1(X1) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3118,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.33/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.33/1.00      | v3_ordinal1(X1) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1696,c_1681]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8984,plain,
% 3.33/1.00      ( X0 = X1
% 3.33/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.33/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.33/1.00      | v3_ordinal1(X1) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_3118,c_1681]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9227,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK5),X0) = X0
% 3.33/1.00      | sK5 = X0
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1678,c_8984]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9255,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 3.33/1.00      | sK5 = sK4 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1677,c_9227]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_25,negated_conjecture,
% 3.33/1.00      ( sK4 != sK5 ),
% 3.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1211,plain,( X0 = X0 ),theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1238,plain,
% 3.33/1.00      ( sK4 = sK4 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1211]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1212,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1955,plain,
% 3.33/1.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1212]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1956,plain,
% 3.33/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1955]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9429,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK5),sK4) = sK4 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9255,c_25,c_1238,c_1956]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9430,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_9429]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_11,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1690,plain,
% 3.33/1.00      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9438,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 3.33/1.00      | r2_hidden(sK4,sK4) != iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(sK5)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_9430,c_1690]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_26,negated_conjecture,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_21,plain,
% 3.33/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_42,plain,
% 3.33/1.00      ( v1_relat_1(k1_wellord2(sK4)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2147,plain,
% 3.33/1.00      ( r2_hidden(sK5,sK4)
% 3.33/1.00      | r2_hidden(sK4,sK5)
% 3.33/1.00      | ~ v3_ordinal1(sK5)
% 3.33/1.00      | ~ v3_ordinal1(sK4)
% 3.33/1.00      | sK4 = sK5 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2280,plain,
% 3.33/1.00      ( ~ r2_hidden(sK5,X0)
% 3.33/1.00      | ~ v3_ordinal1(X0)
% 3.33/1.00      | ~ v3_ordinal1(sK5)
% 3.33/1.00      | k1_wellord1(k1_wellord2(X0),sK5) = sK5 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2283,plain,
% 3.33/1.00      ( ~ r2_hidden(sK5,sK4)
% 3.33/1.00      | ~ v3_ordinal1(sK5)
% 3.33/1.00      | ~ v3_ordinal1(sK4)
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2280]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_12,plain,
% 3.33/1.00      ( ~ r4_wellord1(X0,X1)
% 3.33/1.00      | r4_wellord1(X1,X0)
% 3.33/1.00      | ~ v1_relat_1(X1)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1940,plain,
% 3.33/1.00      ( ~ r4_wellord1(X0,k1_wellord2(X1))
% 3.33/1.00      | r4_wellord1(k1_wellord2(X1),X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2126,plain,
% 3.33/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
% 3.33/1.00      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(X0))
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_1940]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2661,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
% 3.33/1.00      | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(sK5))
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(sK4)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_2126]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2774,plain,
% 3.33/1.00      ( v1_relat_1(k1_wellord2(sK5)) ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_20,plain,
% 3.33/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.33/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.33/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_163,plain,
% 3.33/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_20,c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1,plain,
% 3.33/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1700,plain,
% 3.33/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.33/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 3.33/1.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 3.33/1.00      | ~ v1_relat_1(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1691,plain,
% 3.33/1.00      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 3.33/1.00      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2804,plain,
% 3.33/1.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(X0,X1),X2),X1),X0) = iProver_top
% 3.33/1.00      | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_1700,c_1691]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4,plain,
% 3.33/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.33/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.33/1.00      | ~ v1_relat_1(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1697,plain,
% 3.33/1.00      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 3.33/1.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4105,plain,
% 3.33/1.00      ( r2_hidden(sK0(k1_wellord1(X0,X1),X2),k3_relat_1(X0)) = iProver_top
% 3.33/1.00      | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_2804,c_1697]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_0,plain,
% 3.33/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1701,plain,
% 3.33/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.33/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4844,plain,
% 3.33/1.00      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_4105,c_1701]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4984,plain,
% 3.33/1.00      ( r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) = iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_163,c_4844]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_41,plain,
% 3.33/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5001,plain,
% 3.33/1.00      ( r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_4984,c_41]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_24,plain,
% 3.33/1.00      ( ~ r1_tarski(X0,X1)
% 3.33/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1680,plain,
% 3.33/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.33/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5008,plain,
% 3.33/1.00      ( k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)) = k1_wellord2(k1_wellord1(k1_wellord2(X0),X1)) ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_5001,c_1680]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_13,plain,
% 3.33/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.33/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.33/1.00      | ~ v2_wellord1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_23,plain,
% 3.33/1.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_315,plain,
% 3.33/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.33/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.33/1.00      | ~ v3_ordinal1(X2)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | k1_wellord2(X2) != X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_316,plain,
% 3.33/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.33/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.33/1.00      | ~ v3_ordinal1(X0)
% 3.33/1.00      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_315]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_320,plain,
% 3.33/1.00      ( ~ v3_ordinal1(X0)
% 3.33/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.33/1.00      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_316,c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_321,plain,
% 3.33/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.33/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.33/1.00      | ~ v3_ordinal1(X0) ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_320]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1676,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.33/1.00      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1800,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.33/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_1676,c_163]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5094,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(X0),k1_wellord2(k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.33/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.33/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_5008,c_1800]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9445,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 3.33/1.00      | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) != iProver_top
% 3.33/1.00      | r2_hidden(sK4,sK5) != iProver_top
% 3.33/1.00      | v3_ordinal1(sK5) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_9430,c_5094]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9581,plain,
% 3.33/1.00      ( ~ r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
% 3.33/1.00      | ~ r2_hidden(sK4,sK5)
% 3.33/1.00      | ~ v3_ordinal1(sK5)
% 3.33/1.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 3.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9445]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9821,plain,
% 3.33/1.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9438,c_28,c_27,c_26,c_25,c_42,c_2147,c_2283,c_2661,
% 3.33/1.00                 c_2774,c_9581]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9827,plain,
% 3.33/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.33/1.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_9821,c_1691]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_43,plain,
% 3.33/1.00      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_41]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10142,plain,
% 3.33/1.00      ( r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
% 3.33/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9827,c_43]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10143,plain,
% 3.33/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.33/1.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_10142]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_3,plain,
% 3.33/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.33/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.33/1.00      | ~ v1_relat_1(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1698,plain,
% 3.33/1.00      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 3.33/1.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10151,plain,
% 3.33/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.33/1.00      | r2_hidden(sK5,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_10143,c_1698]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10199,plain,
% 3.33/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.33/1.00      | r2_hidden(sK5,sK4) = iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_10151,c_163]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10225,plain,
% 3.33/1.00      ( r2_hidden(sK5,sK4) = iProver_top
% 3.33/1.00      | r2_hidden(sK4,sK5) != iProver_top
% 3.33/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.33/1.00      inference(instantiation,[status(thm)],[c_10199]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9836,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top
% 3.33/1.00      | r2_hidden(sK5,sK4) != iProver_top
% 3.33/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_9821,c_5094]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_2148,plain,
% 3.33/1.00      ( sK4 = sK5
% 3.33/1.00      | r2_hidden(sK5,sK4) = iProver_top
% 3.33/1.00      | r2_hidden(sK4,sK5) = iProver_top
% 3.33/1.00      | v3_ordinal1(sK5) != iProver_top
% 3.33/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_31,plain,
% 3.33/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_30,plain,
% 3.33/1.00      ( v3_ordinal1(sK5) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_29,plain,
% 3.33/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(contradiction,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(minisat,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_10225,c_9836,c_2148,c_43,c_25,c_31,c_30,c_29]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ General
% 3.33/1.00  
% 3.33/1.00  abstr_ref_over_cycles:                  0
% 3.33/1.00  abstr_ref_under_cycles:                 0
% 3.33/1.00  gc_basic_clause_elim:                   0
% 3.33/1.00  forced_gc_time:                         0
% 3.33/1.00  parsing_time:                           0.009
% 3.33/1.00  unif_index_cands_time:                  0.
% 3.33/1.00  unif_index_add_time:                    0.
% 3.33/1.00  orderings_time:                         0.
% 3.33/1.00  out_proof_time:                         0.009
% 3.33/1.00  total_time:                             0.405
% 3.33/1.00  num_of_symbols:                         48
% 3.33/1.00  num_of_terms:                           12286
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing
% 3.33/1.00  
% 3.33/1.00  num_of_splits:                          0
% 3.33/1.00  num_of_split_atoms:                     0
% 3.33/1.00  num_of_reused_defs:                     0
% 3.33/1.00  num_eq_ax_congr_red:                    24
% 3.33/1.00  num_of_sem_filtered_clauses:            1
% 3.33/1.00  num_of_subtypes:                        0
% 3.33/1.00  monotx_restored_types:                  0
% 3.33/1.00  sat_num_of_epr_types:                   0
% 3.33/1.00  sat_num_of_non_cyclic_types:            0
% 3.33/1.00  sat_guarded_non_collapsed_types:        0
% 3.33/1.00  num_pure_diseq_elim:                    0
% 3.33/1.00  simp_replaced_by:                       0
% 3.33/1.00  res_preprocessed:                       142
% 3.33/1.00  prep_upred:                             0
% 3.33/1.00  prep_unflattend:                        49
% 3.33/1.00  smt_new_axioms:                         0
% 3.33/1.00  pred_elim_cands:                        5
% 3.33/1.00  pred_elim:                              1
% 3.33/1.00  pred_elim_cl:                           1
% 3.33/1.00  pred_elim_cycles:                       3
% 3.33/1.00  merged_defs:                            0
% 3.33/1.00  merged_defs_ncl:                        0
% 3.33/1.00  bin_hyper_res:                          0
% 3.33/1.00  prep_cycles:                            4
% 3.33/1.00  pred_elim_time:                         0.016
% 3.33/1.00  splitting_time:                         0.
% 3.33/1.00  sem_filter_time:                        0.
% 3.33/1.00  monotx_time:                            0.
% 3.33/1.00  subtype_inf_time:                       0.
% 3.33/1.00  
% 3.33/1.00  ------ Problem properties
% 3.33/1.00  
% 3.33/1.00  clauses:                                28
% 3.33/1.00  conjectures:                            4
% 3.33/1.00  epr:                                    6
% 3.33/1.00  horn:                                   19
% 3.33/1.00  ground:                                 4
% 3.33/1.00  unary:                                  6
% 3.33/1.00  binary:                                 4
% 3.33/1.00  lits:                                   83
% 3.33/1.00  lits_eq:                                15
% 3.33/1.00  fd_pure:                                0
% 3.33/1.00  fd_pseudo:                              0
% 3.33/1.00  fd_cond:                                0
% 3.33/1.00  fd_pseudo_cond:                         4
% 3.33/1.00  ac_symbols:                             0
% 3.33/1.00  
% 3.33/1.00  ------ Propositional Solver
% 3.33/1.00  
% 3.33/1.00  prop_solver_calls:                      27
% 3.33/1.00  prop_fast_solver_calls:                 1267
% 3.33/1.00  smt_solver_calls:                       0
% 3.33/1.00  smt_fast_solver_calls:                  0
% 3.33/1.00  prop_num_of_clauses:                    3618
% 3.33/1.00  prop_preprocess_simplified:             10365
% 3.33/1.00  prop_fo_subsumed:                       21
% 3.33/1.00  prop_solver_time:                       0.
% 3.33/1.00  smt_solver_time:                        0.
% 3.33/1.00  smt_fast_solver_time:                   0.
% 3.33/1.00  prop_fast_solver_time:                  0.
% 3.33/1.00  prop_unsat_core_time:                   0.
% 3.33/1.00  
% 3.33/1.00  ------ QBF
% 3.33/1.00  
% 3.33/1.00  qbf_q_res:                              0
% 3.33/1.00  qbf_num_tautologies:                    0
% 3.33/1.00  qbf_prep_cycles:                        0
% 3.33/1.00  
% 3.33/1.00  ------ BMC1
% 3.33/1.00  
% 3.33/1.00  bmc1_current_bound:                     -1
% 3.33/1.00  bmc1_last_solved_bound:                 -1
% 3.33/1.00  bmc1_unsat_core_size:                   -1
% 3.33/1.00  bmc1_unsat_core_parents_size:           -1
% 3.33/1.00  bmc1_merge_next_fun:                    0
% 3.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation
% 3.33/1.00  
% 3.33/1.00  inst_num_of_clauses:                    941
% 3.33/1.00  inst_num_in_passive:                    384
% 3.33/1.00  inst_num_in_active:                     362
% 3.33/1.00  inst_num_in_unprocessed:                195
% 3.33/1.00  inst_num_of_loops:                      430
% 3.33/1.00  inst_num_of_learning_restarts:          0
% 3.33/1.00  inst_num_moves_active_passive:          67
% 3.33/1.00  inst_lit_activity:                      0
% 3.33/1.00  inst_lit_activity_moves:                0
% 3.33/1.00  inst_num_tautologies:                   0
% 3.33/1.00  inst_num_prop_implied:                  0
% 3.33/1.00  inst_num_existing_simplified:           0
% 3.33/1.00  inst_num_eq_res_simplified:             0
% 3.33/1.00  inst_num_child_elim:                    0
% 3.33/1.00  inst_num_of_dismatching_blockings:      594
% 3.33/1.00  inst_num_of_non_proper_insts:           919
% 3.33/1.00  inst_num_of_duplicates:                 0
% 3.33/1.00  inst_inst_num_from_inst_to_res:         0
% 3.33/1.00  inst_dismatching_checking_time:         0.
% 3.33/1.00  
% 3.33/1.00  ------ Resolution
% 3.33/1.00  
% 3.33/1.00  res_num_of_clauses:                     0
% 3.33/1.00  res_num_in_passive:                     0
% 3.33/1.00  res_num_in_active:                      0
% 3.33/1.00  res_num_of_loops:                       146
% 3.33/1.00  res_forward_subset_subsumed:            63
% 3.33/1.00  res_backward_subset_subsumed:           0
% 3.33/1.00  res_forward_subsumed:                   0
% 3.33/1.00  res_backward_subsumed:                  0
% 3.33/1.00  res_forward_subsumption_resolution:     8
% 3.33/1.00  res_backward_subsumption_resolution:    0
% 3.33/1.00  res_clause_to_clause_subsumption:       1218
% 3.33/1.00  res_orphan_elimination:                 0
% 3.33/1.00  res_tautology_del:                      40
% 3.33/1.00  res_num_eq_res_simplified:              0
% 3.33/1.00  res_num_sel_changes:                    0
% 3.33/1.00  res_moves_from_active_to_pass:          0
% 3.33/1.00  
% 3.33/1.00  ------ Superposition
% 3.33/1.00  
% 3.33/1.00  sup_time_total:                         0.
% 3.33/1.00  sup_time_generating:                    0.
% 3.33/1.00  sup_time_sim_full:                      0.
% 3.33/1.00  sup_time_sim_immed:                     0.
% 3.33/1.00  
% 3.33/1.00  sup_num_of_clauses:                     209
% 3.33/1.00  sup_num_in_active:                      85
% 3.33/1.00  sup_num_in_passive:                     124
% 3.33/1.00  sup_num_of_loops:                       85
% 3.33/1.00  sup_fw_superposition:                   94
% 3.33/1.00  sup_bw_superposition:                   186
% 3.33/1.00  sup_immediate_simplified:               53
% 3.33/1.00  sup_given_eliminated:                   0
% 3.33/1.00  comparisons_done:                       0
% 3.33/1.00  comparisons_avoided:                    21
% 3.33/1.00  
% 3.33/1.00  ------ Simplifications
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  sim_fw_subset_subsumed:                 8
% 3.33/1.00  sim_bw_subset_subsumed:                 19
% 3.33/1.00  sim_fw_subsumed:                        4
% 3.33/1.00  sim_bw_subsumed:                        0
% 3.33/1.00  sim_fw_subsumption_res:                 3
% 3.33/1.00  sim_bw_subsumption_res:                 0
% 3.33/1.00  sim_tautology_del:                      7
% 3.33/1.00  sim_eq_tautology_del:                   23
% 3.33/1.00  sim_eq_res_simp:                        0
% 3.33/1.00  sim_fw_demodulated:                     11
% 3.33/1.00  sim_bw_demodulated:                     1
% 3.33/1.00  sim_light_normalised:                   30
% 3.33/1.00  sim_joinable_taut:                      0
% 3.33/1.00  sim_joinable_simp:                      0
% 3.33/1.00  sim_ac_normalised:                      0
% 3.33/1.00  sim_smt_subsumption:                    0
% 3.33/1.00  
%------------------------------------------------------------------------------
