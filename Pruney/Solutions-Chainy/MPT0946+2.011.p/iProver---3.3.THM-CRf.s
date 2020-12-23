%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:43 EST 2020

% Result     : Theorem 19.82s
% Output     : CNFRefutation 19.82s
% Verified   : 
% Statistics : Number of formulae       :  222 (46759 expanded)
%              Number of clauses        :  136 (14843 expanded)
%              Number of leaves         :   24 (9933 expanded)
%              Depth                    :   46
%              Number of atoms          :  941 (231883 expanded)
%              Number of equality atoms :  451 (75565 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK8 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK8))
        & v3_ordinal1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK7 != X1
          & r4_wellord1(k1_wellord2(sK7),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( sK7 != sK8
    & r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
    & v3_ordinal1(sK8)
    & v3_ordinal1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f57,f56])).

fof(f93,plain,(
    v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    v3_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    sK7 != sK8 ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f18])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & r2_hidden(sK6(X0,X1),X0)
            & r2_hidden(sK5(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f54])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f111,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( ! [X2] :
                ( ( r1_tarski(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,k3_relat_1(X0)) )
               => r2_hidden(X2,X1) )
           => r1_tarski(k3_relat_1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),X1)
          | ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & r1_tarski(k1_wellord1(X0,X2),X1)
              & r2_hidden(X2,k3_relat_1(X0)) ) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),X1)
          | ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & r1_tarski(k1_wellord1(X0,X2),X1)
              & r2_hidden(X2,k3_relat_1(X0)) ) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r1_tarski(k1_wellord1(X0,X2),X1)
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_tarski(k1_wellord1(X0,sK4(X0,X1)),X1)
        & r2_hidden(sK4(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),X1)
          | ( ~ r2_hidden(sK4(X0,X1),X1)
            & r1_tarski(k1_wellord1(X0,sK4(X0,X1)),X1)
            & r2_hidden(sK4(X0,X1),k3_relat_1(X0)) ) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),X1)
      | r2_hidden(sK4(X0,X1),k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X3),X1) )
     => ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1),X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,X0)
              & r2_hidden(k4_tarski(X4,X3),X1) )
          & r2_hidden(X3,X0) )
     => ( ? [X4] :
            ( ~ r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X1,X2) = X0
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK1(X0,X1)) = X0
        & r2_hidden(sK1(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X1,sK1(X0,X1)) = X0
            & r2_hidden(sK1(X0,X1),k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ( ~ r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X1)
            & r2_hidden(sK2(X0,X1),X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k3_relat_1(X1) != X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    ! [X6,X5,X1] :
      ( r2_hidden(X6,k3_relat_1(X1))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,k3_relat_1(X1))
      | ~ r1_tarski(k3_relat_1(X1),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),X1)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1094,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_37,negated_conjecture,
    ( v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1062,plain,
    ( v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1063,plain,
    ( v3_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1067,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2764,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1067])).

cnf(c_4901,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_1067])).

cnf(c_5297,plain,
    ( k1_wellord1(k1_wellord2(X0),sK8) = sK8
    | k1_wellord1(k1_wellord2(sK8),X0) = X0
    | sK8 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_4901])).

cnf(c_5325,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | sK8 = sK7 ),
    inference(superposition,[status(thm)],[c_1062,c_5297])).

cnf(c_34,negated_conjecture,
    ( sK7 != sK8 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_129,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_133,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_500,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1505,plain,
    ( sK8 != X0
    | sK7 != X0
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_1506,plain,
    ( sK8 != sK7
    | sK7 = sK8
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_5493,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5325,c_34,c_129,c_133,c_1506])).

cnf(c_5494,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(renaming,[status(thm)],[c_5493])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1092,plain,
    ( k1_wellord1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1090,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3460,plain,
    ( sK0(X0,X1,X2) = X1
    | k1_wellord1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_wellord1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1090])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | sK0(X0,X1,X2) != X1
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_116,plain,
    ( sK0(X0,X1,X2) != X1
    | k1_wellord1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8326,plain,
    ( k1_wellord1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_wellord1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_116])).

cnf(c_8336,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = X0
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r2_hidden(sK0(k1_wellord2(sK8),sK7,X0),X0) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK8),sK7,X0),sK7) = iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5494,c_8326])).

cnf(c_21,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2584,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
    | ~ v1_relat_1(k1_wellord2(sK8))
    | ~ v1_relat_1(k1_wellord2(sK7)) ),
    inference(resolution,[status(thm)],[c_21,c_35])).

cnf(c_30,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_51,plain,
    ( v1_relat_1(k1_wellord2(sK7)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1064,plain,
    ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1076,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2361,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) = iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top
    | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1076])).

cnf(c_2362,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
    | ~ v1_relat_1(k1_wellord2(sK8))
    | ~ v1_relat_1(k1_wellord2(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2361])).

cnf(c_2878,plain,
    ( ~ v1_relat_1(k1_wellord2(sK8))
    | r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2584,c_51,c_2362])).

cnf(c_2879,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
    | ~ v1_relat_1(k1_wellord2(sK8)) ),
    inference(renaming,[status(thm)],[c_2878])).

cnf(c_2884,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2879,c_30])).

cnf(c_2885,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2884])).

cnf(c_29,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_264,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_30])).

cnf(c_20,plain,
    ( r2_hidden(sK4(X0,X1),k3_relat_1(X0))
    | r1_tarski(k3_relat_1(X0),X1)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1077,plain,
    ( r2_hidden(sK4(X0,X1),k3_relat_1(X0)) = iProver_top
    | r1_tarski(k3_relat_1(X0),X1) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2512,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) = iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_1077])).

cnf(c_2530,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2512,c_264])).

cnf(c_50,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4676,plain,
    ( v2_wellord1(k1_wellord2(X0)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2530,c_50])).

cnf(c_4677,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4676])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1089,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4684,plain,
    ( r2_hidden(k4_tarski(sK4(k1_wellord2(k1_wellord1(X0,X1)),X2),X1),X0) = iProver_top
    | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4677,c_1089])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ r1_tarski(k3_relat_1(X1),k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1080,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r2_hidden(X2,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | r1_tarski(k3_relat_1(X1),k3_relat_1(X1)) != iProver_top
    | v2_wellord1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1095,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1329,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r2_hidden(X2,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v2_wellord1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1080,c_1095])).

cnf(c_7480,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(k1_wellord2(k1_wellord1(X1,X0)),X2),k3_relat_1(X1)) = iProver_top
    | r1_tarski(k1_wellord1(X1,X0),X2) = iProver_top
    | v2_wellord1(X1) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4684,c_1329])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | r1_tarski(k3_relat_1(X0),X1)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1079,plain,
    ( r2_hidden(sK4(X0,X1),X1) != iProver_top
    | r1_tarski(k3_relat_1(X0),X1) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_62675,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(k1_wellord1(X1,X0))),k3_relat_1(X1)) = iProver_top
    | v2_wellord1(X1) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7480,c_1079])).

cnf(c_62723,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
    | v2_wellord1(X1) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62675,c_264])).

cnf(c_1068,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_62779,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
    | v2_wellord1(X1) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_62723,c_1068])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1065,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_62787,plain,
    ( k2_wellord1(k1_wellord2(k3_relat_1(X0)),k1_wellord1(X0,X1)) = k1_wellord2(k1_wellord1(X0,X1))
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_62779,c_1065])).

cnf(c_64664,plain,
    ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5494,c_62787])).

cnf(c_64671,plain,
    ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64664,c_264])).

cnf(c_1715,plain,
    ( ~ r2_hidden(sK8,sK7)
    | ~ v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK7)
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3309,plain,
    ( r2_hidden(sK8,sK7)
    | r2_hidden(sK7,sK8)
    | ~ v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK7) ),
    inference(resolution,[status(thm)],[c_3,c_34])).

cnf(c_3327,plain,
    ( r2_hidden(sK8,sK7)
    | r2_hidden(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3309,c_37,c_36])).

cnf(c_32,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4648,plain,
    ( v2_wellord1(k1_wellord2(sK8))
    | ~ v3_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1066,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_62784,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) != iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
    | v2_wellord1(k1_wellord2(X1)) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_264,c_62779])).

cnf(c_62929,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
    | v2_wellord1(k1_wellord2(X1)) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62784,c_264])).

cnf(c_63686,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
    | v2_wellord1(k1_wellord2(X1)) != iProver_top
    | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_62929,c_1068])).

cnf(c_63690,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
    | v2_wellord1(k1_wellord2(X1)) != iProver_top
    | v3_ordinal1(k1_wellord1(k1_wellord2(X1),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_63686])).

cnf(c_63722,plain,
    ( k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)) = k1_wellord2(k1_wellord1(k1_wellord2(X0),X1))
    | r2_hidden(X1,X0) != iProver_top
    | v2_wellord1(k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(k1_wellord1(k1_wellord2(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_63690,c_1065])).

cnf(c_64150,plain,
    ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5494,c_63722])).

cnf(c_64151,plain,
    ( ~ r2_hidden(sK7,sK8)
    | ~ v2_wellord1(k1_wellord2(sK8))
    | ~ v3_ordinal1(sK7)
    | k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_64150])).

cnf(c_68250,plain,
    ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64671,c_37,c_36,c_1715,c_3327,c_4648,c_64151])).

cnf(c_22,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1075,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_68255,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
    | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68250,c_1075])).

cnf(c_68261,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_68255,c_264])).

cnf(c_38,plain,
    ( v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_39,plain,
    ( v3_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1716,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r2_hidden(sK8,sK7) != iProver_top
    | v3_ordinal1(sK8) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_3329,plain,
    ( r2_hidden(sK8,sK7) = iProver_top
    | r2_hidden(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3327])).

cnf(c_3343,plain,
    ( v1_relat_1(k1_wellord2(sK8)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3344,plain,
    ( v1_relat_1(k1_wellord2(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3343])).

cnf(c_4649,plain,
    ( v2_wellord1(k1_wellord2(sK8)) = iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4648])).

cnf(c_68273,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
    | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_68261,c_38,c_39,c_1716,c_3329,c_3344,c_4649])).

cnf(c_68274,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_68273])).

cnf(c_68279,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
    | r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5494,c_68274])).

cnf(c_68538,plain,
    ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8336,c_2885,c_68279])).

cnf(c_68675,plain,
    ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) != iProver_top
    | r2_hidden(sK8,k3_relat_1(k1_wellord2(sK7))) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68538,c_1075])).

cnf(c_69106,plain,
    ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) != iProver_top
    | r2_hidden(sK8,sK7) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_68675,c_264])).

cnf(c_40,plain,
    ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_46,plain,
    ( v2_wellord1(k1_wellord2(sK7)) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_52,plain,
    ( v1_relat_1(k1_wellord2(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_511,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_524,plain,
    ( k1_wellord2(sK7) = k1_wellord2(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_509,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1560,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
    | X1 != k1_wellord2(sK8)
    | X0 != k1_wellord2(sK7) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1749,plain,
    ( r4_wellord1(k1_wellord2(sK7),X0)
    | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
    | X0 != k1_wellord2(sK8)
    | k1_wellord2(sK7) != k1_wellord2(sK7) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_1991,plain,
    ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(X0),sK8))
    | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
    | k2_wellord1(k1_wellord2(X0),sK8) != k1_wellord2(sK8)
    | k1_wellord2(sK7) != k1_wellord2(sK7) ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_1993,plain,
    ( k2_wellord1(k1_wellord2(X0),sK8) != k1_wellord2(sK8)
    | k1_wellord2(sK7) != k1_wellord2(sK7)
    | r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(X0),sK8)) = iProver_top
    | r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1991])).

cnf(c_1995,plain,
    ( k2_wellord1(k1_wellord2(sK7),sK8) != k1_wellord2(sK8)
    | k1_wellord2(sK7) != k1_wellord2(sK7)
    | r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) = iProver_top
    | r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_68689,plain,
    ( k2_wellord1(k1_wellord2(sK7),k1_wellord1(k1_wellord2(sK7),sK8)) = k1_wellord2(k1_wellord1(k1_wellord2(sK7),sK8))
    | r2_hidden(sK8,sK7) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_68538,c_63722])).

cnf(c_68973,plain,
    ( k2_wellord1(k1_wellord2(sK7),sK8) = k1_wellord2(sK8)
    | r2_hidden(sK8,sK7) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_68689,c_68538])).

cnf(c_70133,plain,
    ( r2_hidden(sK8,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69106,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,c_1995,c_68973])).

cnf(c_70141,plain,
    ( sK8 = sK7
    | r2_hidden(sK7,sK8) = iProver_top
    | v3_ordinal1(sK8) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_70133])).

cnf(c_70161,plain,
    ( r2_hidden(sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70141,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,c_1995,c_3329,c_68973,c_69106])).

cnf(c_70166,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
    | v3_ordinal1(sK8) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_70161,c_1067])).

cnf(c_2055,plain,
    ( ~ r2_hidden(sK7,sK8)
    | ~ v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK7)
    | k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2056,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
    | r2_hidden(sK7,sK8) != iProver_top
    | v3_ordinal1(sK8) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_72477,plain,
    ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_70166,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,c_1995,c_2056,c_3329,c_68973,c_69106])).

cnf(c_72484,plain,
    ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_72477,c_62787])).

cnf(c_73405,plain,
    ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),sK7) = k1_wellord2(sK7)
    | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72484,c_72477])).

cnf(c_73406,plain,
    ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7)
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v2_wellord1(k1_wellord2(sK7)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73405,c_264])).

cnf(c_72554,plain,
    ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_72477,c_63722])).

cnf(c_72838,plain,
    ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7)
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72554,c_72477])).

cnf(c_78760,plain,
    ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73406,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,c_1995,c_3329,c_4649,c_68973,c_69106,c_72838])).

cnf(c_72540,plain,
    ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top
    | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_72477,c_1075])).

cnf(c_72969,plain,
    ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top
    | r2_hidden(sK7,sK8) != iProver_top
    | v2_wellord1(k1_wellord2(sK8)) != iProver_top
    | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_72540,c_264])).

cnf(c_74264,plain,
    ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72969,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,c_1995,c_3329,c_3344,c_4649,c_68973,c_69106])).

cnf(c_78763,plain,
    ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_78760,c_74264])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78763,c_2885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.82/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.82/2.99  
% 19.82/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.82/2.99  
% 19.82/2.99  ------  iProver source info
% 19.82/2.99  
% 19.82/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.82/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.82/2.99  git: non_committed_changes: false
% 19.82/2.99  git: last_make_outside_of_git: false
% 19.82/2.99  
% 19.82/2.99  ------ 
% 19.82/2.99  
% 19.82/2.99  ------ Input Options
% 19.82/2.99  
% 19.82/2.99  --out_options                           all
% 19.82/2.99  --tptp_safe_out                         true
% 19.82/2.99  --problem_path                          ""
% 19.82/2.99  --include_path                          ""
% 19.82/2.99  --clausifier                            res/vclausify_rel
% 19.82/2.99  --clausifier_options                    --mode clausify
% 19.82/2.99  --stdin                                 false
% 19.82/2.99  --stats_out                             sel
% 19.82/2.99  
% 19.82/2.99  ------ General Options
% 19.82/2.99  
% 19.82/2.99  --fof                                   false
% 19.82/2.99  --time_out_real                         604.99
% 19.82/2.99  --time_out_virtual                      -1.
% 19.82/2.99  --symbol_type_check                     false
% 19.82/2.99  --clausify_out                          false
% 19.82/2.99  --sig_cnt_out                           false
% 19.82/2.99  --trig_cnt_out                          false
% 19.82/2.99  --trig_cnt_out_tolerance                1.
% 19.82/2.99  --trig_cnt_out_sk_spl                   false
% 19.82/2.99  --abstr_cl_out                          false
% 19.82/2.99  
% 19.82/2.99  ------ Global Options
% 19.82/2.99  
% 19.82/2.99  --schedule                              none
% 19.82/2.99  --add_important_lit                     false
% 19.82/2.99  --prop_solver_per_cl                    1000
% 19.82/2.99  --min_unsat_core                        false
% 19.82/2.99  --soft_assumptions                      false
% 19.82/2.99  --soft_lemma_size                       3
% 19.82/2.99  --prop_impl_unit_size                   0
% 19.82/2.99  --prop_impl_unit                        []
% 19.82/2.99  --share_sel_clauses                     true
% 19.82/2.99  --reset_solvers                         false
% 19.82/2.99  --bc_imp_inh                            [conj_cone]
% 19.82/2.99  --conj_cone_tolerance                   3.
% 19.82/2.99  --extra_neg_conj                        none
% 19.82/2.99  --large_theory_mode                     true
% 19.82/2.99  --prolific_symb_bound                   200
% 19.82/2.99  --lt_threshold                          2000
% 19.82/2.99  --clause_weak_htbl                      true
% 19.82/2.99  --gc_record_bc_elim                     false
% 19.82/2.99  
% 19.82/2.99  ------ Preprocessing Options
% 19.82/2.99  
% 19.82/2.99  --preprocessing_flag                    true
% 19.82/2.99  --time_out_prep_mult                    0.1
% 19.82/2.99  --splitting_mode                        input
% 19.82/2.99  --splitting_grd                         true
% 19.82/2.99  --splitting_cvd                         false
% 19.82/2.99  --splitting_cvd_svl                     false
% 19.82/2.99  --splitting_nvd                         32
% 19.82/2.99  --sub_typing                            true
% 19.82/2.99  --prep_gs_sim                           false
% 19.82/2.99  --prep_unflatten                        true
% 19.82/2.99  --prep_res_sim                          true
% 19.82/2.99  --prep_upred                            true
% 19.82/2.99  --prep_sem_filter                       exhaustive
% 19.82/2.99  --prep_sem_filter_out                   false
% 19.82/2.99  --pred_elim                             false
% 19.82/2.99  --res_sim_input                         true
% 19.82/2.99  --eq_ax_congr_red                       true
% 19.82/2.99  --pure_diseq_elim                       true
% 19.82/2.99  --brand_transform                       false
% 19.82/2.99  --non_eq_to_eq                          false
% 19.82/2.99  --prep_def_merge                        true
% 19.82/2.99  --prep_def_merge_prop_impl              false
% 19.82/2.99  --prep_def_merge_mbd                    true
% 19.82/2.99  --prep_def_merge_tr_red                 false
% 19.82/2.99  --prep_def_merge_tr_cl                  false
% 19.82/2.99  --smt_preprocessing                     true
% 19.82/2.99  --smt_ac_axioms                         fast
% 19.82/2.99  --preprocessed_out                      false
% 19.82/2.99  --preprocessed_stats                    false
% 19.82/2.99  
% 19.82/2.99  ------ Abstraction refinement Options
% 19.82/2.99  
% 19.82/2.99  --abstr_ref                             []
% 19.82/2.99  --abstr_ref_prep                        false
% 19.82/2.99  --abstr_ref_until_sat                   false
% 19.82/2.99  --abstr_ref_sig_restrict                funpre
% 19.82/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.82/2.99  --abstr_ref_under                       []
% 19.82/2.99  
% 19.82/2.99  ------ SAT Options
% 19.82/2.99  
% 19.82/2.99  --sat_mode                              false
% 19.82/2.99  --sat_fm_restart_options                ""
% 19.82/2.99  --sat_gr_def                            false
% 19.82/2.99  --sat_epr_types                         true
% 19.82/2.99  --sat_non_cyclic_types                  false
% 19.82/2.99  --sat_finite_models                     false
% 19.82/2.99  --sat_fm_lemmas                         false
% 19.82/2.99  --sat_fm_prep                           false
% 19.82/2.99  --sat_fm_uc_incr                        true
% 19.82/2.99  --sat_out_model                         small
% 19.82/2.99  --sat_out_clauses                       false
% 19.82/2.99  
% 19.82/2.99  ------ QBF Options
% 19.82/2.99  
% 19.82/2.99  --qbf_mode                              false
% 19.82/2.99  --qbf_elim_univ                         false
% 19.82/2.99  --qbf_dom_inst                          none
% 19.82/2.99  --qbf_dom_pre_inst                      false
% 19.82/2.99  --qbf_sk_in                             false
% 19.82/2.99  --qbf_pred_elim                         true
% 19.82/2.99  --qbf_split                             512
% 19.82/2.99  
% 19.82/2.99  ------ BMC1 Options
% 19.82/2.99  
% 19.82/2.99  --bmc1_incremental                      false
% 19.82/2.99  --bmc1_axioms                           reachable_all
% 19.82/2.99  --bmc1_min_bound                        0
% 19.82/2.99  --bmc1_max_bound                        -1
% 19.82/2.99  --bmc1_max_bound_default                -1
% 19.82/2.99  --bmc1_symbol_reachability              true
% 19.82/2.99  --bmc1_property_lemmas                  false
% 19.82/2.99  --bmc1_k_induction                      false
% 19.82/2.99  --bmc1_non_equiv_states                 false
% 19.82/2.99  --bmc1_deadlock                         false
% 19.82/2.99  --bmc1_ucm                              false
% 19.82/2.99  --bmc1_add_unsat_core                   none
% 19.82/2.99  --bmc1_unsat_core_children              false
% 19.82/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.82/2.99  --bmc1_out_stat                         full
% 19.82/2.99  --bmc1_ground_init                      false
% 19.82/2.99  --bmc1_pre_inst_next_state              false
% 19.82/2.99  --bmc1_pre_inst_state                   false
% 19.82/2.99  --bmc1_pre_inst_reach_state             false
% 19.82/2.99  --bmc1_out_unsat_core                   false
% 19.82/2.99  --bmc1_aig_witness_out                  false
% 19.82/2.99  --bmc1_verbose                          false
% 19.82/2.99  --bmc1_dump_clauses_tptp                false
% 19.82/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.82/2.99  --bmc1_dump_file                        -
% 19.82/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.82/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.82/2.99  --bmc1_ucm_extend_mode                  1
% 19.82/2.99  --bmc1_ucm_init_mode                    2
% 19.82/2.99  --bmc1_ucm_cone_mode                    none
% 19.82/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.82/2.99  --bmc1_ucm_relax_model                  4
% 19.82/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.82/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.82/2.99  --bmc1_ucm_layered_model                none
% 19.82/2.99  --bmc1_ucm_max_lemma_size               10
% 19.82/2.99  
% 19.82/2.99  ------ AIG Options
% 19.82/2.99  
% 19.82/2.99  --aig_mode                              false
% 19.82/2.99  
% 19.82/2.99  ------ Instantiation Options
% 19.82/2.99  
% 19.82/2.99  --instantiation_flag                    true
% 19.82/2.99  --inst_sos_flag                         false
% 19.82/2.99  --inst_sos_phase                        true
% 19.82/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.82/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.82/2.99  --inst_lit_sel_side                     num_symb
% 19.82/2.99  --inst_solver_per_active                1400
% 19.82/2.99  --inst_solver_calls_frac                1.
% 19.82/2.99  --inst_passive_queue_type               priority_queues
% 19.82/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.82/2.99  --inst_passive_queues_freq              [25;2]
% 19.82/2.99  --inst_dismatching                      true
% 19.82/2.99  --inst_eager_unprocessed_to_passive     true
% 19.82/2.99  --inst_prop_sim_given                   true
% 19.82/2.99  --inst_prop_sim_new                     false
% 19.82/2.99  --inst_subs_new                         false
% 19.82/2.99  --inst_eq_res_simp                      false
% 19.82/2.99  --inst_subs_given                       false
% 19.82/2.99  --inst_orphan_elimination               true
% 19.82/2.99  --inst_learning_loop_flag               true
% 19.82/2.99  --inst_learning_start                   3000
% 19.82/2.99  --inst_learning_factor                  2
% 19.82/2.99  --inst_start_prop_sim_after_learn       3
% 19.82/2.99  --inst_sel_renew                        solver
% 19.82/2.99  --inst_lit_activity_flag                true
% 19.82/2.99  --inst_restr_to_given                   false
% 19.82/2.99  --inst_activity_threshold               500
% 19.82/2.99  --inst_out_proof                        true
% 19.82/2.99  
% 19.82/2.99  ------ Resolution Options
% 19.82/2.99  
% 19.82/2.99  --resolution_flag                       true
% 19.82/2.99  --res_lit_sel                           adaptive
% 19.82/2.99  --res_lit_sel_side                      none
% 19.82/2.99  --res_ordering                          kbo
% 19.82/2.99  --res_to_prop_solver                    active
% 19.82/2.99  --res_prop_simpl_new                    false
% 19.82/2.99  --res_prop_simpl_given                  true
% 19.82/2.99  --res_passive_queue_type                priority_queues
% 19.82/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.82/2.99  --res_passive_queues_freq               [15;5]
% 19.82/2.99  --res_forward_subs                      full
% 19.82/2.99  --res_backward_subs                     full
% 19.82/2.99  --res_forward_subs_resolution           true
% 19.82/2.99  --res_backward_subs_resolution          true
% 19.82/2.99  --res_orphan_elimination                true
% 19.82/2.99  --res_time_limit                        2.
% 19.82/2.99  --res_out_proof                         true
% 19.82/2.99  
% 19.82/2.99  ------ Superposition Options
% 19.82/2.99  
% 19.82/2.99  --superposition_flag                    true
% 19.82/2.99  --sup_passive_queue_type                priority_queues
% 19.82/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.82/2.99  --sup_passive_queues_freq               [1;4]
% 19.82/2.99  --demod_completeness_check              fast
% 19.82/2.99  --demod_use_ground                      true
% 19.82/2.99  --sup_to_prop_solver                    passive
% 19.82/2.99  --sup_prop_simpl_new                    true
% 19.82/2.99  --sup_prop_simpl_given                  true
% 19.82/2.99  --sup_fun_splitting                     false
% 19.82/2.99  --sup_smt_interval                      50000
% 19.82/2.99  
% 19.82/2.99  ------ Superposition Simplification Setup
% 19.82/2.99  
% 19.82/2.99  --sup_indices_passive                   []
% 19.82/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.82/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/2.99  --sup_full_bw                           [BwDemod]
% 19.82/2.99  --sup_immed_triv                        [TrivRules]
% 19.82/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.82/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/2.99  --sup_immed_bw_main                     []
% 19.82/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.82/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.82/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.82/2.99  
% 19.82/2.99  ------ Combination Options
% 19.82/2.99  
% 19.82/2.99  --comb_res_mult                         3
% 19.82/2.99  --comb_sup_mult                         2
% 19.82/2.99  --comb_inst_mult                        10
% 19.82/2.99  
% 19.82/2.99  ------ Debug Options
% 19.82/2.99  
% 19.82/2.99  --dbg_backtrace                         false
% 19.82/2.99  --dbg_dump_prop_clauses                 false
% 19.82/2.99  --dbg_dump_prop_clauses_file            -
% 19.82/2.99  --dbg_out_stat                          false
% 19.82/2.99  ------ Parsing...
% 19.82/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.82/2.99  
% 19.82/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.82/2.99  
% 19.82/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.82/2.99  
% 19.82/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.82/2.99  ------ Proving...
% 19.82/2.99  ------ Problem Properties 
% 19.82/2.99  
% 19.82/2.99  
% 19.82/2.99  clauses                                 37
% 19.82/2.99  conjectures                             4
% 19.82/2.99  EPR                                     7
% 19.82/2.99  Horn                                    21
% 19.82/2.99  unary                                   7
% 19.82/2.99  binary                                  3
% 19.82/2.99  lits                                    138
% 19.82/2.99  lits eq                                 25
% 19.82/2.99  fd_pure                                 0
% 19.82/2.99  fd_pseudo                               0
% 19.82/2.99  fd_cond                                 0
% 19.82/2.99  fd_pseudo_cond                          8
% 19.82/2.99  AC symbols                              0
% 19.82/2.99  
% 19.82/2.99  ------ Input Options Time Limit: Unbounded
% 19.82/2.99  
% 19.82/2.99  
% 19.82/2.99  ------ 
% 19.82/2.99  Current options:
% 19.82/2.99  ------ 
% 19.82/2.99  
% 19.82/2.99  ------ Input Options
% 19.82/2.99  
% 19.82/2.99  --out_options                           all
% 19.82/2.99  --tptp_safe_out                         true
% 19.82/2.99  --problem_path                          ""
% 19.82/2.99  --include_path                          ""
% 19.82/2.99  --clausifier                            res/vclausify_rel
% 19.82/2.99  --clausifier_options                    --mode clausify
% 19.82/2.99  --stdin                                 false
% 19.82/2.99  --stats_out                             sel
% 19.82/2.99  
% 19.82/2.99  ------ General Options
% 19.82/2.99  
% 19.82/2.99  --fof                                   false
% 19.82/2.99  --time_out_real                         604.99
% 19.82/2.99  --time_out_virtual                      -1.
% 19.82/2.99  --symbol_type_check                     false
% 19.82/2.99  --clausify_out                          false
% 19.82/2.99  --sig_cnt_out                           false
% 19.82/2.99  --trig_cnt_out                          false
% 19.82/2.99  --trig_cnt_out_tolerance                1.
% 19.82/2.99  --trig_cnt_out_sk_spl                   false
% 19.82/2.99  --abstr_cl_out                          false
% 19.82/2.99  
% 19.82/2.99  ------ Global Options
% 19.82/2.99  
% 19.82/2.99  --schedule                              none
% 19.82/2.99  --add_important_lit                     false
% 19.82/2.99  --prop_solver_per_cl                    1000
% 19.82/2.99  --min_unsat_core                        false
% 19.82/2.99  --soft_assumptions                      false
% 19.82/2.99  --soft_lemma_size                       3
% 19.82/2.99  --prop_impl_unit_size                   0
% 19.82/2.99  --prop_impl_unit                        []
% 19.82/2.99  --share_sel_clauses                     true
% 19.82/2.99  --reset_solvers                         false
% 19.82/2.99  --bc_imp_inh                            [conj_cone]
% 19.82/2.99  --conj_cone_tolerance                   3.
% 19.82/2.99  --extra_neg_conj                        none
% 19.82/2.99  --large_theory_mode                     true
% 19.82/2.99  --prolific_symb_bound                   200
% 19.82/2.99  --lt_threshold                          2000
% 19.82/2.99  --clause_weak_htbl                      true
% 19.82/2.99  --gc_record_bc_elim                     false
% 19.82/2.99  
% 19.82/2.99  ------ Preprocessing Options
% 19.82/2.99  
% 19.82/2.99  --preprocessing_flag                    true
% 19.82/2.99  --time_out_prep_mult                    0.1
% 19.82/2.99  --splitting_mode                        input
% 19.82/2.99  --splitting_grd                         true
% 19.82/2.99  --splitting_cvd                         false
% 19.82/2.99  --splitting_cvd_svl                     false
% 19.82/2.99  --splitting_nvd                         32
% 19.82/2.99  --sub_typing                            true
% 19.82/2.99  --prep_gs_sim                           false
% 19.82/2.99  --prep_unflatten                        true
% 19.82/2.99  --prep_res_sim                          true
% 19.82/2.99  --prep_upred                            true
% 19.82/2.99  --prep_sem_filter                       exhaustive
% 19.82/2.99  --prep_sem_filter_out                   false
% 19.82/2.99  --pred_elim                             false
% 19.82/2.99  --res_sim_input                         true
% 19.82/2.99  --eq_ax_congr_red                       true
% 19.82/2.99  --pure_diseq_elim                       true
% 19.82/2.99  --brand_transform                       false
% 19.82/3.00  --non_eq_to_eq                          false
% 19.82/3.00  --prep_def_merge                        true
% 19.82/3.00  --prep_def_merge_prop_impl              false
% 19.82/3.00  --prep_def_merge_mbd                    true
% 19.82/3.00  --prep_def_merge_tr_red                 false
% 19.82/3.00  --prep_def_merge_tr_cl                  false
% 19.82/3.00  --smt_preprocessing                     true
% 19.82/3.00  --smt_ac_axioms                         fast
% 19.82/3.00  --preprocessed_out                      false
% 19.82/3.00  --preprocessed_stats                    false
% 19.82/3.00  
% 19.82/3.00  ------ Abstraction refinement Options
% 19.82/3.00  
% 19.82/3.00  --abstr_ref                             []
% 19.82/3.00  --abstr_ref_prep                        false
% 19.82/3.00  --abstr_ref_until_sat                   false
% 19.82/3.00  --abstr_ref_sig_restrict                funpre
% 19.82/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.82/3.00  --abstr_ref_under                       []
% 19.82/3.00  
% 19.82/3.00  ------ SAT Options
% 19.82/3.00  
% 19.82/3.00  --sat_mode                              false
% 19.82/3.00  --sat_fm_restart_options                ""
% 19.82/3.00  --sat_gr_def                            false
% 19.82/3.00  --sat_epr_types                         true
% 19.82/3.00  --sat_non_cyclic_types                  false
% 19.82/3.00  --sat_finite_models                     false
% 19.82/3.00  --sat_fm_lemmas                         false
% 19.82/3.00  --sat_fm_prep                           false
% 19.82/3.00  --sat_fm_uc_incr                        true
% 19.82/3.00  --sat_out_model                         small
% 19.82/3.00  --sat_out_clauses                       false
% 19.82/3.00  
% 19.82/3.00  ------ QBF Options
% 19.82/3.00  
% 19.82/3.00  --qbf_mode                              false
% 19.82/3.00  --qbf_elim_univ                         false
% 19.82/3.00  --qbf_dom_inst                          none
% 19.82/3.00  --qbf_dom_pre_inst                      false
% 19.82/3.00  --qbf_sk_in                             false
% 19.82/3.00  --qbf_pred_elim                         true
% 19.82/3.00  --qbf_split                             512
% 19.82/3.00  
% 19.82/3.00  ------ BMC1 Options
% 19.82/3.00  
% 19.82/3.00  --bmc1_incremental                      false
% 19.82/3.00  --bmc1_axioms                           reachable_all
% 19.82/3.00  --bmc1_min_bound                        0
% 19.82/3.00  --bmc1_max_bound                        -1
% 19.82/3.00  --bmc1_max_bound_default                -1
% 19.82/3.00  --bmc1_symbol_reachability              true
% 19.82/3.00  --bmc1_property_lemmas                  false
% 19.82/3.00  --bmc1_k_induction                      false
% 19.82/3.00  --bmc1_non_equiv_states                 false
% 19.82/3.00  --bmc1_deadlock                         false
% 19.82/3.00  --bmc1_ucm                              false
% 19.82/3.00  --bmc1_add_unsat_core                   none
% 19.82/3.00  --bmc1_unsat_core_children              false
% 19.82/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.82/3.00  --bmc1_out_stat                         full
% 19.82/3.00  --bmc1_ground_init                      false
% 19.82/3.00  --bmc1_pre_inst_next_state              false
% 19.82/3.00  --bmc1_pre_inst_state                   false
% 19.82/3.00  --bmc1_pre_inst_reach_state             false
% 19.82/3.00  --bmc1_out_unsat_core                   false
% 19.82/3.00  --bmc1_aig_witness_out                  false
% 19.82/3.00  --bmc1_verbose                          false
% 19.82/3.00  --bmc1_dump_clauses_tptp                false
% 19.82/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.82/3.00  --bmc1_dump_file                        -
% 19.82/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.82/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.82/3.00  --bmc1_ucm_extend_mode                  1
% 19.82/3.00  --bmc1_ucm_init_mode                    2
% 19.82/3.00  --bmc1_ucm_cone_mode                    none
% 19.82/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.82/3.00  --bmc1_ucm_relax_model                  4
% 19.82/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.82/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.82/3.00  --bmc1_ucm_layered_model                none
% 19.82/3.00  --bmc1_ucm_max_lemma_size               10
% 19.82/3.00  
% 19.82/3.00  ------ AIG Options
% 19.82/3.00  
% 19.82/3.00  --aig_mode                              false
% 19.82/3.00  
% 19.82/3.00  ------ Instantiation Options
% 19.82/3.00  
% 19.82/3.00  --instantiation_flag                    true
% 19.82/3.00  --inst_sos_flag                         false
% 19.82/3.00  --inst_sos_phase                        true
% 19.82/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.82/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.82/3.00  --inst_lit_sel_side                     num_symb
% 19.82/3.00  --inst_solver_per_active                1400
% 19.82/3.00  --inst_solver_calls_frac                1.
% 19.82/3.00  --inst_passive_queue_type               priority_queues
% 19.82/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.82/3.00  --inst_passive_queues_freq              [25;2]
% 19.82/3.00  --inst_dismatching                      true
% 19.82/3.00  --inst_eager_unprocessed_to_passive     true
% 19.82/3.00  --inst_prop_sim_given                   true
% 19.82/3.00  --inst_prop_sim_new                     false
% 19.82/3.00  --inst_subs_new                         false
% 19.82/3.00  --inst_eq_res_simp                      false
% 19.82/3.00  --inst_subs_given                       false
% 19.82/3.00  --inst_orphan_elimination               true
% 19.82/3.00  --inst_learning_loop_flag               true
% 19.82/3.00  --inst_learning_start                   3000
% 19.82/3.00  --inst_learning_factor                  2
% 19.82/3.00  --inst_start_prop_sim_after_learn       3
% 19.82/3.00  --inst_sel_renew                        solver
% 19.82/3.00  --inst_lit_activity_flag                true
% 19.82/3.00  --inst_restr_to_given                   false
% 19.82/3.00  --inst_activity_threshold               500
% 19.82/3.00  --inst_out_proof                        true
% 19.82/3.00  
% 19.82/3.00  ------ Resolution Options
% 19.82/3.00  
% 19.82/3.00  --resolution_flag                       true
% 19.82/3.00  --res_lit_sel                           adaptive
% 19.82/3.00  --res_lit_sel_side                      none
% 19.82/3.00  --res_ordering                          kbo
% 19.82/3.00  --res_to_prop_solver                    active
% 19.82/3.00  --res_prop_simpl_new                    false
% 19.82/3.00  --res_prop_simpl_given                  true
% 19.82/3.00  --res_passive_queue_type                priority_queues
% 19.82/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.82/3.00  --res_passive_queues_freq               [15;5]
% 19.82/3.00  --res_forward_subs                      full
% 19.82/3.00  --res_backward_subs                     full
% 19.82/3.00  --res_forward_subs_resolution           true
% 19.82/3.00  --res_backward_subs_resolution          true
% 19.82/3.00  --res_orphan_elimination                true
% 19.82/3.00  --res_time_limit                        2.
% 19.82/3.00  --res_out_proof                         true
% 19.82/3.00  
% 19.82/3.00  ------ Superposition Options
% 19.82/3.00  
% 19.82/3.00  --superposition_flag                    true
% 19.82/3.00  --sup_passive_queue_type                priority_queues
% 19.82/3.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.82/3.00  --sup_passive_queues_freq               [1;4]
% 19.82/3.00  --demod_completeness_check              fast
% 19.82/3.00  --demod_use_ground                      true
% 19.82/3.00  --sup_to_prop_solver                    passive
% 19.82/3.00  --sup_prop_simpl_new                    true
% 19.82/3.00  --sup_prop_simpl_given                  true
% 19.82/3.00  --sup_fun_splitting                     false
% 19.82/3.00  --sup_smt_interval                      50000
% 19.82/3.00  
% 19.82/3.00  ------ Superposition Simplification Setup
% 19.82/3.00  
% 19.82/3.00  --sup_indices_passive                   []
% 19.82/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.82/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.82/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/3.00  --sup_full_bw                           [BwDemod]
% 19.82/3.00  --sup_immed_triv                        [TrivRules]
% 19.82/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.82/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/3.00  --sup_immed_bw_main                     []
% 19.82/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.82/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.82/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.82/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.82/3.00  
% 19.82/3.00  ------ Combination Options
% 19.82/3.00  
% 19.82/3.00  --comb_res_mult                         3
% 19.82/3.00  --comb_sup_mult                         2
% 19.82/3.00  --comb_inst_mult                        10
% 19.82/3.00  
% 19.82/3.00  ------ Debug Options
% 19.82/3.00  
% 19.82/3.00  --dbg_backtrace                         false
% 19.82/3.00  --dbg_dump_prop_clauses                 false
% 19.82/3.00  --dbg_dump_prop_clauses_file            -
% 19.82/3.00  --dbg_out_stat                          false
% 19.82/3.00  
% 19.82/3.00  
% 19.82/3.00  
% 19.82/3.00  
% 19.82/3.00  ------ Proving...
% 19.82/3.00  
% 19.82/3.00  
% 19.82/3.00  % SZS status Theorem for theBenchmark.p
% 19.82/3.00  
% 19.82/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.82/3.00  
% 19.82/3.00  fof(f2,axiom,(
% 19.82/3.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f16,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f2])).
% 19.82/3.00  
% 19.82/3.00  fof(f17,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 19.82/3.00    inference(flattening,[],[f16])).
% 19.82/3.00  
% 19.82/3.00  fof(f62,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f17])).
% 19.82/3.00  
% 19.82/3.00  fof(f13,conjecture,(
% 19.82/3.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f14,negated_conjecture,(
% 19.82/3.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 19.82/3.00    inference(negated_conjecture,[],[f13])).
% 19.82/3.00  
% 19.82/3.00  fof(f33,plain,(
% 19.82/3.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f14])).
% 19.82/3.00  
% 19.82/3.00  fof(f34,plain,(
% 19.82/3.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 19.82/3.00    inference(flattening,[],[f33])).
% 19.82/3.00  
% 19.82/3.00  fof(f57,plain,(
% 19.82/3.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK8 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK8)) & v3_ordinal1(sK8))) )),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f56,plain,(
% 19.82/3.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK7 != X1 & r4_wellord1(k1_wellord2(sK7),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK7))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f58,plain,(
% 19.82/3.00    (sK7 != sK8 & r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) & v3_ordinal1(sK8)) & v3_ordinal1(sK7)),
% 19.82/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f57,f56])).
% 19.82/3.00  
% 19.82/3.00  fof(f93,plain,(
% 19.82/3.00    v3_ordinal1(sK7)),
% 19.82/3.00    inference(cnf_transformation,[],[f58])).
% 19.82/3.00  
% 19.82/3.00  fof(f94,plain,(
% 19.82/3.00    v3_ordinal1(sK8)),
% 19.82/3.00    inference(cnf_transformation,[],[f58])).
% 19.82/3.00  
% 19.82/3.00  fof(f10,axiom,(
% 19.82/3.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f29,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f10])).
% 19.82/3.00  
% 19.82/3.00  fof(f30,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 19.82/3.00    inference(flattening,[],[f29])).
% 19.82/3.00  
% 19.82/3.00  fof(f90,plain,(
% 19.82/3.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f30])).
% 19.82/3.00  
% 19.82/3.00  fof(f96,plain,(
% 19.82/3.00    sK7 != sK8),
% 19.82/3.00    inference(cnf_transformation,[],[f58])).
% 19.82/3.00  
% 19.82/3.00  fof(f1,axiom,(
% 19.82/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f35,plain,(
% 19.82/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.82/3.00    inference(nnf_transformation,[],[f1])).
% 19.82/3.00  
% 19.82/3.00  fof(f36,plain,(
% 19.82/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.82/3.00    inference(flattening,[],[f35])).
% 19.82/3.00  
% 19.82/3.00  fof(f59,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.82/3.00    inference(cnf_transformation,[],[f36])).
% 19.82/3.00  
% 19.82/3.00  fof(f98,plain,(
% 19.82/3.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.82/3.00    inference(equality_resolution,[],[f59])).
% 19.82/3.00  
% 19.82/3.00  fof(f61,plain,(
% 19.82/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f36])).
% 19.82/3.00  
% 19.82/3.00  fof(f3,axiom,(
% 19.82/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f18,plain,(
% 19.82/3.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f3])).
% 19.82/3.00  
% 19.82/3.00  fof(f37,plain,(
% 19.82/3.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(nnf_transformation,[],[f18])).
% 19.82/3.00  
% 19.82/3.00  fof(f38,plain,(
% 19.82/3.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(flattening,[],[f37])).
% 19.82/3.00  
% 19.82/3.00  fof(f39,plain,(
% 19.82/3.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(rectify,[],[f38])).
% 19.82/3.00  
% 19.82/3.00  fof(f40,plain,(
% 19.82/3.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f41,plain,(
% 19.82/3.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 19.82/3.00  
% 19.82/3.00  fof(f67,plain,(
% 19.82/3.00    ( ! [X2,X0,X1] : (k1_wellord1(X0,X1) = X2 | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f41])).
% 19.82/3.00  
% 19.82/3.00  fof(f65,plain,(
% 19.82/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f41])).
% 19.82/3.00  
% 19.82/3.00  fof(f99,plain,(
% 19.82/3.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(equality_resolution,[],[f65])).
% 19.82/3.00  
% 19.82/3.00  fof(f66,plain,(
% 19.82/3.00    ( ! [X2,X0,X1] : (k1_wellord1(X0,X1) = X2 | sK0(X0,X1,X2) != X1 | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f41])).
% 19.82/3.00  
% 19.82/3.00  fof(f6,axiom,(
% 19.82/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f23,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f6])).
% 19.82/3.00  
% 19.82/3.00  fof(f24,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(flattening,[],[f23])).
% 19.82/3.00  
% 19.82/3.00  fof(f80,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f24])).
% 19.82/3.00  
% 19.82/3.00  fof(f95,plain,(
% 19.82/3.00    r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))),
% 19.82/3.00    inference(cnf_transformation,[],[f58])).
% 19.82/3.00  
% 19.82/3.00  fof(f9,axiom,(
% 19.82/3.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f89,plain,(
% 19.82/3.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 19.82/3.00    inference(cnf_transformation,[],[f9])).
% 19.82/3.00  
% 19.82/3.00  fof(f8,axiom,(
% 19.82/3.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f27,plain,(
% 19.82/3.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(ennf_transformation,[],[f8])).
% 19.82/3.00  
% 19.82/3.00  fof(f28,plain,(
% 19.82/3.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(flattening,[],[f27])).
% 19.82/3.00  
% 19.82/3.00  fof(f51,plain,(
% 19.82/3.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(nnf_transformation,[],[f28])).
% 19.82/3.00  
% 19.82/3.00  fof(f52,plain,(
% 19.82/3.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(flattening,[],[f51])).
% 19.82/3.00  
% 19.82/3.00  fof(f53,plain,(
% 19.82/3.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(rectify,[],[f52])).
% 19.82/3.00  
% 19.82/3.00  fof(f54,plain,(
% 19.82/3.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK5(X0,X1),sK6(X0,X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & (r1_tarski(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),X0)))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f55,plain,(
% 19.82/3.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK5(X0,X1),sK6(X0,X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & (r1_tarski(sK5(X0,X1),sK6(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f54])).
% 19.82/3.00  
% 19.82/3.00  fof(f82,plain,(
% 19.82/3.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f55])).
% 19.82/3.00  
% 19.82/3.00  fof(f111,plain,(
% 19.82/3.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 19.82/3.00    inference(equality_resolution,[],[f82])).
% 19.82/3.00  
% 19.82/3.00  fof(f5,axiom,(
% 19.82/3.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : (! [X2] : ((r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0))) => r2_hidden(X2,X1)) => r1_tarski(k3_relat_1(X0),X1))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f21,plain,(
% 19.82/3.00    ! [X0] : ((! [X1] : (r1_tarski(k3_relat_1(X0),X1) | ? [X2] : (~r2_hidden(X2,X1) & (r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0))))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f5])).
% 19.82/3.00  
% 19.82/3.00  fof(f22,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),X1) | ? [X2] : (~r2_hidden(X2,X1) & r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0)))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(flattening,[],[f21])).
% 19.82/3.00  
% 19.82/3.00  fof(f49,plain,(
% 19.82/3.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r1_tarski(k1_wellord1(X0,X2),X1) & r2_hidden(X2,k3_relat_1(X0))) => (~r2_hidden(sK4(X0,X1),X1) & r1_tarski(k1_wellord1(X0,sK4(X0,X1)),X1) & r2_hidden(sK4(X0,X1),k3_relat_1(X0))))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f50,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),X1) | (~r2_hidden(sK4(X0,X1),X1) & r1_tarski(k1_wellord1(X0,sK4(X0,X1)),X1) & r2_hidden(sK4(X0,X1),k3_relat_1(X0)))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f49])).
% 19.82/3.00  
% 19.82/3.00  fof(f77,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),X1) | r2_hidden(sK4(X0,X1),k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f50])).
% 19.82/3.00  
% 19.82/3.00  fof(f64,plain,(
% 19.82/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f41])).
% 19.82/3.00  
% 19.82/3.00  fof(f100,plain,(
% 19.82/3.00    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(equality_resolution,[],[f64])).
% 19.82/3.00  
% 19.82/3.00  fof(f4,axiom,(
% 19.82/3.00    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f15,plain,(
% 19.82/3.00    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 19.82/3.00    inference(rectify,[],[f4])).
% 19.82/3.00  
% 19.82/3.00  fof(f19,plain,(
% 19.82/3.00    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(ennf_transformation,[],[f15])).
% 19.82/3.00  
% 19.82/3.00  fof(f20,plain,(
% 19.82/3.00    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(flattening,[],[f19])).
% 19.82/3.00  
% 19.82/3.00  fof(f42,plain,(
% 19.82/3.00    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(nnf_transformation,[],[f20])).
% 19.82/3.00  
% 19.82/3.00  fof(f43,plain,(
% 19.82/3.00    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(flattening,[],[f42])).
% 19.82/3.00  
% 19.82/3.00  fof(f44,plain,(
% 19.82/3.00    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(rectify,[],[f43])).
% 19.82/3.00  
% 19.82/3.00  fof(f47,plain,(
% 19.82/3.00    ( ! [X3] : (! [X1,X0] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) => (~r2_hidden(sK3(X0,X1),X0) & r2_hidden(k4_tarski(sK3(X0,X1),X3),X1)))) )),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f46,plain,(
% 19.82/3.00    ! [X1,X0] : (? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0)) => (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f45,plain,(
% 19.82/3.00    ! [X1,X0] : (? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) => (k1_wellord1(X1,sK1(X0,X1)) = X0 & r2_hidden(sK1(X0,X1),k3_relat_1(X1))))),
% 19.82/3.00    introduced(choice_axiom,[])).
% 19.82/3.00  
% 19.82/3.00  fof(f48,plain,(
% 19.82/3.00    ! [X0,X1] : ((((k1_wellord1(X1,sK1(X0,X1)) = X0 & r2_hidden(sK1(X0,X1),k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ((~r2_hidden(sK3(X0,X1),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 19.82/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).
% 19.82/3.00  
% 19.82/3.00  fof(f69,plain,(
% 19.82/3.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,X0) | k3_relat_1(X1) != X0 | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f48])).
% 19.82/3.00  
% 19.82/3.00  fof(f104,plain,(
% 19.82/3.00    ( ! [X6,X5,X1] : (r2_hidden(X6,k3_relat_1(X1)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,k3_relat_1(X1)) | ~r1_tarski(k3_relat_1(X1),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 19.82/3.00    inference(equality_resolution,[],[f69])).
% 19.82/3.00  
% 19.82/3.00  fof(f60,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.82/3.00    inference(cnf_transformation,[],[f36])).
% 19.82/3.00  
% 19.82/3.00  fof(f97,plain,(
% 19.82/3.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.82/3.00    inference(equality_resolution,[],[f60])).
% 19.82/3.00  
% 19.82/3.00  fof(f79,plain,(
% 19.82/3.00    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),X1) | ~r2_hidden(sK4(X0,X1),X1) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f50])).
% 19.82/3.00  
% 19.82/3.00  fof(f12,axiom,(
% 19.82/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f32,plain,(
% 19.82/3.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 19.82/3.00    inference(ennf_transformation,[],[f12])).
% 19.82/3.00  
% 19.82/3.00  fof(f92,plain,(
% 19.82/3.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f32])).
% 19.82/3.00  
% 19.82/3.00  fof(f11,axiom,(
% 19.82/3.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f31,plain,(
% 19.82/3.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f11])).
% 19.82/3.00  
% 19.82/3.00  fof(f91,plain,(
% 19.82/3.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f31])).
% 19.82/3.00  
% 19.82/3.00  fof(f7,axiom,(
% 19.82/3.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 19.82/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.82/3.00  
% 19.82/3.00  fof(f25,plain,(
% 19.82/3.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(ennf_transformation,[],[f7])).
% 19.82/3.00  
% 19.82/3.00  fof(f26,plain,(
% 19.82/3.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 19.82/3.00    inference(flattening,[],[f25])).
% 19.82/3.00  
% 19.82/3.00  fof(f81,plain,(
% 19.82/3.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 19.82/3.00    inference(cnf_transformation,[],[f26])).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3,plain,
% 19.82/3.00      ( r2_hidden(X0,X1)
% 19.82/3.00      | r2_hidden(X1,X0)
% 19.82/3.00      | ~ v3_ordinal1(X1)
% 19.82/3.00      | ~ v3_ordinal1(X0)
% 19.82/3.00      | X1 = X0 ),
% 19.82/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1094,plain,
% 19.82/3.00      ( X0 = X1
% 19.82/3.00      | r2_hidden(X1,X0) = iProver_top
% 19.82/3.00      | r2_hidden(X0,X1) = iProver_top
% 19.82/3.00      | v3_ordinal1(X1) != iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_37,negated_conjecture,
% 19.82/3.00      ( v3_ordinal1(sK7) ),
% 19.82/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1062,plain,
% 19.82/3.00      ( v3_ordinal1(sK7) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_36,negated_conjecture,
% 19.82/3.00      ( v3_ordinal1(sK8) ),
% 19.82/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1063,plain,
% 19.82/3.00      ( v3_ordinal1(sK8) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_31,plain,
% 19.82/3.00      ( ~ r2_hidden(X0,X1)
% 19.82/3.00      | ~ v3_ordinal1(X1)
% 19.82/3.00      | ~ v3_ordinal1(X0)
% 19.82/3.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 19.82/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1067,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 19.82/3.00      | r2_hidden(X1,X0) != iProver_top
% 19.82/3.00      | v3_ordinal1(X1) != iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2764,plain,
% 19.82/3.00      ( X0 = X1
% 19.82/3.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 19.82/3.00      | r2_hidden(X0,X1) = iProver_top
% 19.82/3.00      | v3_ordinal1(X1) != iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1094,c_1067]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4901,plain,
% 19.82/3.00      ( X0 = X1
% 19.82/3.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 19.82/3.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 19.82/3.00      | v3_ordinal1(X1) != iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_2764,c_1067]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_5297,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(X0),sK8) = sK8
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK8),X0) = X0
% 19.82/3.00      | sK8 = X0
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1063,c_4901]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_5325,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | sK8 = sK7 ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1062,c_5297]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_34,negated_conjecture,
% 19.82/3.00      ( sK7 != sK8 ),
% 19.82/3.00      inference(cnf_transformation,[],[f96]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2,plain,
% 19.82/3.00      ( r1_tarski(X0,X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f98]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_129,plain,
% 19.82/3.00      ( r1_tarski(sK7,sK7) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_0,plain,
% 19.82/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.82/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_133,plain,
% 19.82/3.00      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_500,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1505,plain,
% 19.82/3.00      ( sK8 != X0 | sK7 != X0 | sK7 = sK8 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_500]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1506,plain,
% 19.82/3.00      ( sK8 != sK7 | sK7 = sK8 | sK7 != sK7 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_1505]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_5493,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_5325,c_34,c_129,c_133,c_1506]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_5494,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(renaming,[status(thm)],[c_5493]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_5,plain,
% 19.82/3.00      ( r2_hidden(sK0(X0,X1,X2),X2)
% 19.82/3.00      | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
% 19.82/3.00      | ~ v1_relat_1(X0)
% 19.82/3.00      | k1_wellord1(X0,X1) = X2 ),
% 19.82/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1092,plain,
% 19.82/3.00      ( k1_wellord1(X0,X1) = X2
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.82/3.00      | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) = iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_7,plain,
% 19.82/3.00      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 19.82/3.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.82/3.00      | ~ v1_relat_1(X1)
% 19.82/3.00      | X0 = X2 ),
% 19.82/3.00      inference(cnf_transformation,[],[f99]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1090,plain,
% 19.82/3.00      ( X0 = X1
% 19.82/3.00      | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
% 19.82/3.00      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 19.82/3.00      | v1_relat_1(X2) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3460,plain,
% 19.82/3.00      ( sK0(X0,X1,X2) = X1
% 19.82/3.00      | k1_wellord1(X0,X1) = X2
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),k1_wellord1(X0,X1)) = iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1092,c_1090]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_6,plain,
% 19.82/3.00      ( r2_hidden(sK0(X0,X1,X2),X2)
% 19.82/3.00      | ~ v1_relat_1(X0)
% 19.82/3.00      | sK0(X0,X1,X2) != X1
% 19.82/3.00      | k1_wellord1(X0,X1) = X2 ),
% 19.82/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_116,plain,
% 19.82/3.00      ( sK0(X0,X1,X2) != X1
% 19.82/3.00      | k1_wellord1(X0,X1) = X2
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_8326,plain,
% 19.82/3.00      ( k1_wellord1(X0,X1) = X2
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 19.82/3.00      | r2_hidden(sK0(X0,X1,X2),k1_wellord1(X0,X1)) = iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_3460,c_116]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_8336,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = X0
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r2_hidden(sK0(k1_wellord2(sK8),sK7,X0),X0) = iProver_top
% 19.82/3.00      | r2_hidden(sK0(k1_wellord2(sK8),sK7,X0),sK7) = iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_5494,c_8326]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_21,plain,
% 19.82/3.00      ( ~ r4_wellord1(X0,X1)
% 19.82/3.00      | r4_wellord1(X1,X0)
% 19.82/3.00      | ~ v1_relat_1(X0)
% 19.82/3.00      | ~ v1_relat_1(X1) ),
% 19.82/3.00      inference(cnf_transformation,[],[f80]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_35,negated_conjecture,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) ),
% 19.82/3.00      inference(cnf_transformation,[],[f95]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2584,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
% 19.82/3.00      | ~ v1_relat_1(k1_wellord2(sK8))
% 19.82/3.00      | ~ v1_relat_1(k1_wellord2(sK7)) ),
% 19.82/3.00      inference(resolution,[status(thm)],[c_21,c_35]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_30,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 19.82/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_51,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(sK7)) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1064,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1076,plain,
% 19.82/3.00      ( r4_wellord1(X0,X1) != iProver_top
% 19.82/3.00      | r4_wellord1(X1,X0) = iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2361,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) = iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1064,c_1076]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2362,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
% 19.82/3.00      | ~ v1_relat_1(k1_wellord2(sK8))
% 19.82/3.00      | ~ v1_relat_1(k1_wellord2(sK7)) ),
% 19.82/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_2361]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2878,plain,
% 19.82/3.00      ( ~ v1_relat_1(k1_wellord2(sK8))
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_2584,c_51,c_2362]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2879,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7))
% 19.82/3.00      | ~ v1_relat_1(k1_wellord2(sK8)) ),
% 19.82/3.00      inference(renaming,[status(thm)],[c_2878]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2884,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) ),
% 19.82/3.00      inference(forward_subsumption_resolution,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_2879,c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2885,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_2884]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_29,plain,
% 19.82/3.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 19.82/3.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 19.82/3.00      inference(cnf_transformation,[],[f111]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_264,plain,
% 19.82/3.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_29,c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_20,plain,
% 19.82/3.00      ( r2_hidden(sK4(X0,X1),k3_relat_1(X0))
% 19.82/3.00      | r1_tarski(k3_relat_1(X0),X1)
% 19.82/3.00      | ~ v2_wellord1(X0)
% 19.82/3.00      | ~ v1_relat_1(X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1077,plain,
% 19.82/3.00      ( r2_hidden(sK4(X0,X1),k3_relat_1(X0)) = iProver_top
% 19.82/3.00      | r1_tarski(k3_relat_1(X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(X0) != iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2512,plain,
% 19.82/3.00      ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
% 19.82/3.00      | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X0)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_264,c_1077]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2530,plain,
% 19.82/3.00      ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
% 19.82/3.00      | r1_tarski(X0,X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X0)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 19.82/3.00      inference(light_normalisation,[status(thm)],[c_2512,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_50,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4676,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(X0)) != iProver_top
% 19.82/3.00      | r1_tarski(X0,X1) = iProver_top
% 19.82/3.00      | r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_2530,c_50]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4677,plain,
% 19.82/3.00      ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
% 19.82/3.00      | r1_tarski(X0,X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X0)) != iProver_top ),
% 19.82/3.00      inference(renaming,[status(thm)],[c_4676]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_8,plain,
% 19.82/3.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 19.82/3.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 19.82/3.00      | ~ v1_relat_1(X1) ),
% 19.82/3.00      inference(cnf_transformation,[],[f100]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1089,plain,
% 19.82/3.00      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 19.82/3.00      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4684,plain,
% 19.82/3.00      ( r2_hidden(k4_tarski(sK4(k1_wellord2(k1_wellord1(X0,X1)),X2),X1),X0) = iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X0,X1))) != iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_4677,c_1089]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_17,plain,
% 19.82/3.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 19.82/3.00      | r2_hidden(X2,k3_relat_1(X1))
% 19.82/3.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.82/3.00      | ~ r1_tarski(k3_relat_1(X1),k3_relat_1(X1))
% 19.82/3.00      | ~ v2_wellord1(X1)
% 19.82/3.00      | ~ v1_relat_1(X1) ),
% 19.82/3.00      inference(cnf_transformation,[],[f104]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1080,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r2_hidden(X2,k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 19.82/3.00      | r1_tarski(k3_relat_1(X1),k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1,plain,
% 19.82/3.00      ( r1_tarski(X0,X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f97]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1095,plain,
% 19.82/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1329,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r2_hidden(X2,k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(forward_subsumption_resolution,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_1080,c_1095]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_7480,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r2_hidden(sK4(k1_wellord2(k1_wellord1(X1,X0)),X2),k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(X1,X0),X2) = iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_4684,c_1329]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_18,plain,
% 19.82/3.00      ( ~ r2_hidden(sK4(X0,X1),X1)
% 19.82/3.00      | r1_tarski(k3_relat_1(X0),X1)
% 19.82/3.00      | ~ v2_wellord1(X0)
% 19.82/3.00      | ~ v1_relat_1(X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f79]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1079,plain,
% 19.82/3.00      ( r2_hidden(sK4(X0,X1),X1) != iProver_top
% 19.82/3.00      | r1_tarski(k3_relat_1(X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(X0) != iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62675,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | r1_tarski(k3_relat_1(k1_wellord2(k1_wellord1(X1,X0))),k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_7480,c_1079]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62723,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_62675,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1068,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62779,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) = iProver_top
% 19.82/3.00      | v2_wellord1(X1) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X1,X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.82/3.00      inference(forward_subsumption_resolution,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_62723,c_1068]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_33,plain,
% 19.82/3.00      ( ~ r1_tarski(X0,X1)
% 19.82/3.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f92]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1065,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 19.82/3.00      | r1_tarski(X1,X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62787,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(k3_relat_1(X0)),k1_wellord1(X0,X1)) = k1_wellord2(k1_wellord1(X0,X1))
% 19.82/3.00      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 19.82/3.00      | v2_wellord1(X0) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(X0,X1))) != iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_62779,c_1065]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_64664,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_5494,c_62787]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_64671,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_64664,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1715,plain,
% 19.82/3.00      ( ~ r2_hidden(sK8,sK7)
% 19.82/3.00      | ~ v3_ordinal1(sK8)
% 19.82/3.00      | ~ v3_ordinal1(sK7)
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_31]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3309,plain,
% 19.82/3.00      ( r2_hidden(sK8,sK7)
% 19.82/3.00      | r2_hidden(sK7,sK8)
% 19.82/3.00      | ~ v3_ordinal1(sK8)
% 19.82/3.00      | ~ v3_ordinal1(sK7) ),
% 19.82/3.00      inference(resolution,[status(thm)],[c_3,c_34]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3327,plain,
% 19.82/3.00      ( r2_hidden(sK8,sK7) | r2_hidden(sK7,sK8) ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_3309,c_37,c_36]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_32,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4648,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(sK8)) | ~ v3_ordinal1(sK8) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_32]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1066,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62784,plain,
% 19.82/3.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X1)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_264,c_62779]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_62929,plain,
% 19.82/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X1)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_62784,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_63686,plain,
% 19.82/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X1)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) != iProver_top ),
% 19.82/3.00      inference(forward_subsumption_resolution,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_62929,c_1068]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_63690,plain,
% 19.82/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.82/3.00      | r1_tarski(k1_wellord1(k1_wellord2(X1),X0),X1) = iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X1)) != iProver_top
% 19.82/3.00      | v3_ordinal1(k1_wellord1(k1_wellord2(X1),X0)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1066,c_63686]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_63722,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)) = k1_wellord2(k1_wellord1(k1_wellord2(X0),X1))
% 19.82/3.00      | r2_hidden(X1,X0) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(X0)) != iProver_top
% 19.82/3.00      | v3_ordinal1(k1_wellord1(k1_wellord2(X0),X1)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_63690,c_1065]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_64150,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_5494,c_63722]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_64151,plain,
% 19.82/3.00      ( ~ r2_hidden(sK7,sK8)
% 19.82/3.00      | ~ v2_wellord1(k1_wellord2(sK8))
% 19.82/3.00      | ~ v3_ordinal1(sK7)
% 19.82/3.00      | k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_64150]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68250,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_64671,c_37,c_36,c_1715,c_3327,c_4648,c_64151]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_22,plain,
% 19.82/3.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 19.82/3.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 19.82/3.00      | ~ v2_wellord1(X0)
% 19.82/3.00      | ~ v1_relat_1(X0) ),
% 19.82/3.00      inference(cnf_transformation,[],[f81]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1075,plain,
% 19.82/3.00      ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
% 19.82/3.00      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 19.82/3.00      | v2_wellord1(X0) != iProver_top
% 19.82/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68255,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
% 19.82/3.00      | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_68250,c_1075]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68261,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_68255,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_38,plain,
% 19.82/3.00      ( v3_ordinal1(sK7) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_39,plain,
% 19.82/3.00      ( v3_ordinal1(sK8) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1716,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r2_hidden(sK8,sK7) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3329,plain,
% 19.82/3.00      ( r2_hidden(sK8,sK7) = iProver_top
% 19.82/3.00      | r2_hidden(sK7,sK8) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_3327]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3343,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(sK8)) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_30]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_3344,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(sK8)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_3343]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_4649,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(sK8)) = iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_4648]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68273,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_68261,c_38,c_39,c_1716,c_3329,c_3344,c_4649]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68274,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK8),k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))) != iProver_top ),
% 19.82/3.00      inference(renaming,[status(thm)],[c_68273]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68279,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_5494,c_68274]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68538,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK7),sK8) = sK8 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_8336,c_2885,c_68279]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68675,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) != iProver_top
% 19.82/3.00      | r2_hidden(sK8,k3_relat_1(k1_wellord2(sK7))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_68538,c_1075]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_69106,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) != iProver_top
% 19.82/3.00      | r2_hidden(sK8,sK7) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK7)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_68675,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_40,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) = iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_44,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 19.82/3.00      | v3_ordinal1(X0) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_46,plain,
% 19.82/3.00      ( v2_wellord1(k1_wellord2(sK7)) = iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_44]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_52,plain,
% 19.82/3.00      ( v1_relat_1(k1_wellord2(sK7)) = iProver_top ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_50]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_511,plain,
% 19.82/3.00      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 19.82/3.00      theory(equality) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_524,plain,
% 19.82/3.00      ( k1_wellord2(sK7) = k1_wellord2(sK7) | sK7 != sK7 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_511]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_509,plain,
% 19.82/3.00      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.82/3.00      theory(equality) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1560,plain,
% 19.82/3.00      ( r4_wellord1(X0,X1)
% 19.82/3.00      | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
% 19.82/3.00      | X1 != k1_wellord2(sK8)
% 19.82/3.00      | X0 != k1_wellord2(sK7) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_509]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1749,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),X0)
% 19.82/3.00      | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
% 19.82/3.00      | X0 != k1_wellord2(sK8)
% 19.82/3.00      | k1_wellord2(sK7) != k1_wellord2(sK7) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_1560]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1991,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(X0),sK8))
% 19.82/3.00      | ~ r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8))
% 19.82/3.00      | k2_wellord1(k1_wellord2(X0),sK8) != k1_wellord2(sK8)
% 19.82/3.00      | k1_wellord2(sK7) != k1_wellord2(sK7) ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_1749]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1993,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(X0),sK8) != k1_wellord2(sK8)
% 19.82/3.00      | k1_wellord2(sK7) != k1_wellord2(sK7)
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(X0),sK8)) = iProver_top
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_1991]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_1995,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK7),sK8) != k1_wellord2(sK8)
% 19.82/3.00      | k1_wellord2(sK7) != k1_wellord2(sK7)
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK7),k2_wellord1(k1_wellord2(sK7),sK8)) = iProver_top
% 19.82/3.00      | r4_wellord1(k1_wellord2(sK7),k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_1993]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68689,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK7),k1_wellord1(k1_wellord2(sK7),sK8)) = k1_wellord2(k1_wellord1(k1_wellord2(sK7),sK8))
% 19.82/3.00      | r2_hidden(sK8,sK7) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_68538,c_63722]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_68973,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK7),sK8) = k1_wellord2(sK8)
% 19.82/3.00      | r2_hidden(sK8,sK7) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top ),
% 19.82/3.00      inference(light_normalisation,[status(thm)],[c_68689,c_68538]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_70133,plain,
% 19.82/3.00      ( r2_hidden(sK8,sK7) != iProver_top ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_69106,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,
% 19.82/3.00                 c_1995,c_68973]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_70141,plain,
% 19.82/3.00      ( sK8 = sK7
% 19.82/3.00      | r2_hidden(sK7,sK8) = iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_1094,c_70133]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_70161,plain,
% 19.82/3.00      ( r2_hidden(sK7,sK8) = iProver_top ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_70141,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,
% 19.82/3.00                 c_1995,c_3329,c_68973,c_69106]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_70166,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_70161,c_1067]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2055,plain,
% 19.82/3.00      ( ~ r2_hidden(sK7,sK8)
% 19.82/3.00      | ~ v3_ordinal1(sK8)
% 19.82/3.00      | ~ v3_ordinal1(sK7)
% 19.82/3.00      | k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
% 19.82/3.00      inference(instantiation,[status(thm)],[c_31]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_2056,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK8) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72477,plain,
% 19.82/3.00      ( k1_wellord1(k1_wellord2(sK8),sK7) = sK7 ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_70166,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,
% 19.82/3.00                 c_1995,c_2056,c_3329,c_68973,c_69106]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72484,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_72477,c_62787]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_73405,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(k3_relat_1(k1_wellord2(sK8))),sK7) = k1_wellord2(sK7)
% 19.82/3.00      | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(light_normalisation,[status(thm)],[c_72484,c_72477]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_73406,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7)
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK7)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_73405,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72554,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),k1_wellord1(k1_wellord2(sK8),sK7)) = k1_wellord2(k1_wellord1(k1_wellord2(sK8),sK7))
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_72477,c_63722]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72838,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7)
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v3_ordinal1(sK7) != iProver_top ),
% 19.82/3.00      inference(light_normalisation,[status(thm)],[c_72554,c_72477]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_78760,plain,
% 19.82/3.00      ( k2_wellord1(k1_wellord2(sK8),sK7) = k1_wellord2(sK7) ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_73406,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,
% 19.82/3.00                 c_1995,c_3329,c_4649,c_68973,c_69106,c_72838]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72540,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top
% 19.82/3.00      | r2_hidden(sK7,k3_relat_1(k1_wellord2(sK8))) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(superposition,[status(thm)],[c_72477,c_1075]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_72969,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top
% 19.82/3.00      | r2_hidden(sK7,sK8) != iProver_top
% 19.82/3.00      | v2_wellord1(k1_wellord2(sK8)) != iProver_top
% 19.82/3.00      | v1_relat_1(k1_wellord2(sK8)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_72540,c_264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_74264,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k2_wellord1(k1_wellord2(sK8),sK7)) != iProver_top ),
% 19.82/3.00      inference(global_propositional_subsumption,
% 19.82/3.00                [status(thm)],
% 19.82/3.00                [c_72969,c_38,c_39,c_40,c_46,c_52,c_129,c_133,c_524,
% 19.82/3.00                 c_1995,c_3329,c_3344,c_4649,c_68973,c_69106]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(c_78763,plain,
% 19.82/3.00      ( r4_wellord1(k1_wellord2(sK8),k1_wellord2(sK7)) != iProver_top ),
% 19.82/3.00      inference(demodulation,[status(thm)],[c_78760,c_74264]) ).
% 19.82/3.00  
% 19.82/3.00  cnf(contradiction,plain,
% 19.82/3.00      ( $false ),
% 19.82/3.00      inference(minisat,[status(thm)],[c_78763,c_2885]) ).
% 19.82/3.00  
% 19.82/3.00  
% 19.82/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.82/3.00  
% 19.82/3.00  ------                               Statistics
% 19.82/3.00  
% 19.82/3.00  ------ Selected
% 19.82/3.00  
% 19.82/3.00  total_time:                             2.264
% 19.82/3.00  
%------------------------------------------------------------------------------
