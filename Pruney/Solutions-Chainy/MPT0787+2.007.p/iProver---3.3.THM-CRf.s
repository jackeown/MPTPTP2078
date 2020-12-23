%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:31 EST 2020

% Result     : Theorem 27.57s
% Output     : CNFRefutation 27.57s
% Verified   : 
% Statistics : Number of formulae       :  217 (3666 expanded)
%              Number of clauses        :  134 ( 924 expanded)
%              Number of leaves         :   21 ( 657 expanded)
%              Depth                    :   32
%              Number of atoms          :  960 (22836 expanded)
%              Number of equality atoms :  221 (2088 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(rectify,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X3),X1) )
     => ( ~ r2_hidden(sK10(X0,X1),X0)
        & r2_hidden(k4_tarski(sK10(X0,X1),X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,X0)
              & r2_hidden(k4_tarski(X4,X3),X1) )
          & r2_hidden(X3,X0) )
     => ( ? [X4] :
            ( ~ r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,sK9(X0,X1)),X1) )
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X1,X2) = X0
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK8(X0,X1)) = X0
        & r2_hidden(sK8(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X1,sK8(X0,X1)) = X0
            & r2_hidden(sK8(X0,X1),k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ( ~ r2_hidden(sK10(X0,X1),X0)
            & r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X1)
            & r2_hidden(sK9(X0,X1),X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f50,f53,f52,f51])).

fof(f90,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k1_wellord1(X1,X7) != X0
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X6,X7,X5,X1] :
      ( r2_hidden(X6,k1_wellord1(X1,X7))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,k1_wellord1(X1,X7))
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f56,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
        | ~ r2_hidden(k4_tarski(sK11,sK12),sK13) )
      & ( r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
        | r2_hidden(k4_tarski(sK11,sK12),sK13) )
      & r2_hidden(sK12,k3_relat_1(sK13))
      & r2_hidden(sK11,k3_relat_1(sK13))
      & v2_wellord1(sK13)
      & v1_relat_1(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
      | ~ r2_hidden(k4_tarski(sK11,sK12),sK13) )
    & ( r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
      | r2_hidden(k4_tarski(sK11,sK12),sK13) )
    & r2_hidden(sK12,k3_relat_1(sK13))
    & r2_hidden(sK11,k3_relat_1(sK13))
    & v2_wellord1(sK13)
    & v1_relat_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f56,f57])).

fof(f98,plain,(
    v2_wellord1(sK13) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    v1_relat_1(sK13) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,
    ( r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
    | r2_hidden(k4_tarski(sK11,sK12),sK13) ),
    inference(cnf_transformation,[],[f58])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f45,f46])).

fof(f83,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).

fof(f79,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,
    ( ~ r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12))
    | ~ r2_hidden(k4_tarski(sK11,sK12),sK13) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    r2_hidden(sK11,k3_relat_1(sK13)) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    r2_hidden(sK12,k3_relat_1(sK13)) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f105,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f106,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f105])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_42,negated_conjecture,
    ( v2_wellord1(sK13) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_757,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_42])).

cnf(c_758,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
    | r2_hidden(X2,k1_wellord1(sK13,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(X2,X0),sK13)
    | ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13))
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_43,negated_conjecture,
    ( v1_relat_1(sK13) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_760,plain,
    ( ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(X2,X0),sK13)
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | r2_hidden(X2,k1_wellord1(sK13,X1))
    | ~ r2_hidden(X0,k1_wellord1(sK13,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_43])).

cnf(c_761,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
    | r2_hidden(X2,k1_wellord1(sK13,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(X2,X0),sK13)
    | ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13)) ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_95486,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,sK11))
    | r2_hidden(X1,k1_wellord1(sK13,sK11))
    | ~ r2_hidden(k4_tarski(X1,X0),sK13)
    | ~ r2_hidden(sK11,k3_relat_1(sK13))
    | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_96099,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,sK11))
    | ~ r2_hidden(k4_tarski(sK11,X0),sK13)
    | r2_hidden(sK11,k1_wellord1(sK13,sK11))
    | ~ r2_hidden(sK11,k3_relat_1(sK13))
    | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_95486])).

cnf(c_98356,plain,
    ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
    | ~ r2_hidden(sK12,k1_wellord1(sK13,sK11))
    | r2_hidden(sK11,k1_wellord1(sK13,sK11))
    | ~ r2_hidden(sK11,k3_relat_1(sK13))
    | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_96099])).

cnf(c_4,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1377,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_43])).

cnf(c_1378,plain,
    ( r2_hidden(X0,k3_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
    inference(unflattening,[status(thm)],[c_1377])).

cnf(c_48638,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,k3_relat_1(sK13)),X1),sK13)
    | r2_hidden(sK0(X0,k3_relat_1(sK13)),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_71036,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),sK11),sK13)
    | r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_48638])).

cnf(c_39,negated_conjecture,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13)
    | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3405,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1306,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_43])).

cnf(c_1307,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X1),sK13)
    | r2_hidden(k4_tarski(X1,X0),sK13)
    | ~ v6_relat_2(sK13)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1306])).

cnf(c_13,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_746,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_42])).

cnf(c_747,plain,
    ( v6_relat_2(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_117,plain,
    ( v6_relat_2(sK13)
    | ~ v2_wellord1(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_749,plain,
    ( v6_relat_2(sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_747,c_43,c_42,c_117])).

cnf(c_1243,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_749])).

cnf(c_1244,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X1),sK13)
    | r2_hidden(k4_tarski(X1,X0),sK13)
    | ~ v1_relat_1(sK13)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1309,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK13)
    | r2_hidden(k4_tarski(X0,X1),sK13)
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | ~ r2_hidden(X0,k3_relat_1(sK13))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1307,c_43,c_1244])).

cnf(c_1310,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | ~ r2_hidden(X1,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X1,X0),sK13)
    | r2_hidden(k4_tarski(X0,X1),sK13)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1309])).

cnf(c_3393,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK13) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1362,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_43])).

cnf(c_1363,plain,
    ( r2_hidden(X0,k1_wellord1(sK13,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK13)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_3390,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK13,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_5475,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(sK13,X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_3393,c_3390])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3408,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1352,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_43])).

cnf(c_1353,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
    | r2_hidden(k4_tarski(X0,X1),sK13) ),
    inference(unflattening,[status(thm)],[c_1352])).

cnf(c_3391,plain,
    ( r2_hidden(X0,k1_wellord1(sK13,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_4263,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),X1),X0),sK13) = iProver_top
    | r1_tarski(k1_wellord1(sK13,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_3391])).

cnf(c_23,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1467,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK13 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_43])).

cnf(c_1468,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | r2_hidden(k4_tarski(X0,X2),sK13)
    | ~ v8_relat_2(sK13) ),
    inference(unflattening,[status(thm)],[c_1467])).

cnf(c_15,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_735,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_42])).

cnf(c_736,plain,
    ( v8_relat_2(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_111,plain,
    ( v8_relat_2(sK13)
    | ~ v2_wellord1(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_738,plain,
    ( v8_relat_2(sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_43,c_42,c_111])).

cnf(c_1083,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK13 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_738])).

cnf(c_1084,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | r2_hidden(k4_tarski(X0,X2),sK13)
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_1083])).

cnf(c_1086,plain,
    ( r2_hidden(k4_tarski(X0,X2),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_43])).

cnf(c_1087,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | r2_hidden(k4_tarski(X0,X2),sK13) ),
    inference(renaming,[status(thm)],[c_1086])).

cnf(c_1470,plain,
    ( r2_hidden(k4_tarski(X0,X2),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_43,c_1084])).

cnf(c_1471,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
    | ~ r2_hidden(k4_tarski(X1,X2),sK13)
    | r2_hidden(k4_tarski(X0,X2),sK13) ),
    inference(renaming,[status(thm)],[c_1470])).

cnf(c_3394,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),sK13) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_4743,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),X2),X1),sK13) = iProver_top
    | r1_tarski(k1_wellord1(sK13,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4263,c_3394])).

cnf(c_8244,plain,
    ( sK0(k1_wellord1(sK13,X0),X1) = X2
    | r2_hidden(k4_tarski(X0,X2),sK13) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK13,X0),X1),k1_wellord1(sK13,X2)) = iProver_top
    | r1_tarski(k1_wellord1(sK13,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4743,c_3390])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3409,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22063,plain,
    ( sK0(k1_wellord1(sK13,X0),k1_wellord1(sK13,X1)) = X1
    | r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
    | r1_tarski(k1_wellord1(sK13,X0),k1_wellord1(sK13,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8244,c_3409])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
    | ~ r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3406,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22327,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_22063,c_3406])).

cnf(c_22412,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | sK12 = sK11
    | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top
    | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5475,c_22327])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK11,k3_relat_1(sK13)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_46,plain,
    ( r2_hidden(sK11,k3_relat_1(sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK12,k3_relat_1(sK13)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_47,plain,
    ( r2_hidden(sK12,k3_relat_1(sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2843,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2864,plain,
    ( sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1329,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_43])).

cnf(c_1330,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X0),sK13)
    | ~ v1_relat_2(sK13) ),
    inference(unflattening,[status(thm)],[c_1329])).

cnf(c_16,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_724,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_42])).

cnf(c_725,plain,
    ( v1_relat_2(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_108,plain,
    ( v1_relat_2(sK13)
    | ~ v2_wellord1(sK13)
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_727,plain,
    ( v1_relat_2(sK13) ),
    inference(global_propositional_subsumption,[status(thm)],[c_725,c_43,c_42,c_108])).

cnf(c_998,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_727])).

cnf(c_999,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X0),sK13)
    | ~ v1_relat_1(sK13) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1003,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK13)
    | ~ r2_hidden(X0,k3_relat_1(sK13)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_43])).

cnf(c_1004,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X0),sK13) ),
    inference(renaming,[status(thm)],[c_1003])).

cnf(c_1332,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK13)
    | ~ r2_hidden(X0,k3_relat_1(sK13)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_43,c_999])).

cnf(c_1333,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,X0),sK13) ),
    inference(renaming,[status(thm)],[c_1332])).

cnf(c_3478,plain,
    ( r2_hidden(k4_tarski(sK11,sK11),sK13)
    | ~ r2_hidden(sK11,k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_3479,plain,
    ( r2_hidden(k4_tarski(sK11,sK11),sK13) = iProver_top
    | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3478])).

cnf(c_2846,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3460,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK11,sK12),sK13)
    | k4_tarski(sK11,sK12) != X0
    | sK13 != X1 ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_3544,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13)
    | ~ r2_hidden(k4_tarski(sK11,sK11),sK13)
    | k4_tarski(sK11,sK12) != k4_tarski(sK11,sK11)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_3545,plain,
    ( k4_tarski(sK11,sK12) != k4_tarski(sK11,sK11)
    | sK13 != sK13
    | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK11),sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3544])).

cnf(c_2848,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_3649,plain,
    ( k4_tarski(sK11,sK12) = k4_tarski(sK11,sK11)
    | sK12 != sK11
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_4660,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_23507,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22412,c_46,c_47,c_2864,c_3479,c_3545,c_3649,c_4660,c_22327])).

cnf(c_23513,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(k4_tarski(sK12,sK11),sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_23507,c_3391])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3407,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23608,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(k4_tarski(sK12,sK11),X0) = iProver_top
    | r1_tarski(sK13,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23513,c_3407])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1343,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK13 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_43])).

cnf(c_1344,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK13,X0)) ),
    inference(unflattening,[status(thm)],[c_1343])).

cnf(c_4186,plain,
    ( ~ r2_hidden(sK12,k1_wellord1(sK13,sK12)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_22357,plain,
    ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
    | sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22327])).

cnf(c_23511,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(sK12,X0) = iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23507,c_3407])).

cnf(c_23767,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
    | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
    | r2_hidden(sK12,k1_wellord1(sK13,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3405,c_23511])).

cnf(c_23777,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13)
    | r2_hidden(sK12,k1_wellord1(sK13,sK12))
    | sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23767])).

cnf(c_23782,plain,
    ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23608,c_4186,c_22357,c_23777])).

cnf(c_23792,plain,
    ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23782,c_3408])).

cnf(c_49,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3475,plain,
    ( r2_hidden(k4_tarski(sK12,sK12),sK13)
    | ~ r2_hidden(sK12,k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_3476,plain,
    ( r2_hidden(k4_tarski(sK12,sK12),sK13) = iProver_top
    | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3475])).

cnf(c_3541,plain,
    ( ~ r2_hidden(k4_tarski(sK12,sK12),sK13)
    | r2_hidden(k4_tarski(sK11,sK12),sK13)
    | k4_tarski(sK11,sK12) != k4_tarski(sK12,sK12)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_3542,plain,
    ( k4_tarski(sK11,sK12) != k4_tarski(sK12,sK12)
    | sK13 != sK13
    | r2_hidden(k4_tarski(sK12,sK12),sK13) != iProver_top
    | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3541])).

cnf(c_3640,plain,
    ( k4_tarski(sK11,sK12) = k4_tarski(sK12,sK12)
    | sK12 != sK12
    | sK11 != sK12 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_4656,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_3841,plain,
    ( ~ r2_hidden(k4_tarski(sK12,X0),sK13)
    | r2_hidden(sK12,k1_wellord1(sK13,X0))
    | X0 = sK12 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_5271,plain,
    ( ~ r2_hidden(k4_tarski(sK12,sK11),sK13)
    | r2_hidden(sK12,k1_wellord1(sK13,sK11))
    | sK11 = sK12 ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_5273,plain,
    ( sK11 = sK12
    | r2_hidden(k4_tarski(sK12,sK11),sK13) != iProver_top
    | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5271])).

cnf(c_3840,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK13))
    | r2_hidden(k4_tarski(X0,sK12),sK13)
    | r2_hidden(k4_tarski(sK12,X0),sK13)
    | ~ r2_hidden(sK12,k3_relat_1(sK13))
    | X0 = sK12 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_5504,plain,
    ( r2_hidden(k4_tarski(sK12,sK11),sK13)
    | r2_hidden(k4_tarski(sK11,sK12),sK13)
    | ~ r2_hidden(sK12,k3_relat_1(sK13))
    | ~ r2_hidden(sK11,k3_relat_1(sK13))
    | sK11 = sK12 ),
    inference(instantiation,[status(thm)],[c_3840])).

cnf(c_5505,plain,
    ( sK11 = sK12
    | r2_hidden(k4_tarski(sK12,sK11),sK13) = iProver_top
    | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
    | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top
    | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5504])).

cnf(c_23962,plain,
    ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23792,c_46,c_47,c_49,c_2864,c_3476,c_3542,c_3640,c_4656,c_5273,c_5505])).

cnf(c_23966,plain,
    ( r2_hidden(sK12,X0) = iProver_top
    | r1_tarski(k1_wellord1(sK13,sK11),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23962,c_3407])).

cnf(c_23977,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
    | r2_hidden(sK12,k1_wellord1(sK13,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3405,c_23966])).

cnf(c_23987,plain,
    ( r2_hidden(k4_tarski(sK11,sK12),sK13)
    | r2_hidden(sK12,k1_wellord1(sK13,sK12)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23977])).

cnf(c_23964,plain,
    ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23962])).

cnf(c_6047,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),k3_relat_1(sK13)),X0),sK13)
    | ~ r2_hidden(sK0(k1_wellord1(sK13,X0),k3_relat_1(sK13)),k1_wellord1(sK13,X0)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_10151,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),sK11),sK13)
    | ~ r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k1_wellord1(sK13,sK11)) ),
    inference(instantiation,[status(thm)],[c_6047])).

cnf(c_4232,plain,
    ( ~ r2_hidden(sK11,k1_wellord1(sK13,sK11)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_3621,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k3_relat_1(sK13))
    | r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3622,plain,
    ( r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k1_wellord1(sK13,sK11))
    | r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98356,c_71036,c_23987,c_23964,c_10151,c_4232,c_4186,c_3621,c_3622,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 27.57/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.57/3.98  
% 27.57/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.57/3.98  
% 27.57/3.98  ------  iProver source info
% 27.57/3.98  
% 27.57/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.57/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.57/3.98  git: non_committed_changes: false
% 27.57/3.98  git: last_make_outside_of_git: false
% 27.57/3.98  
% 27.57/3.98  ------ 
% 27.57/3.98  
% 27.57/3.98  ------ Input Options
% 27.57/3.98  
% 27.57/3.98  --out_options                           all
% 27.57/3.98  --tptp_safe_out                         true
% 27.57/3.98  --problem_path                          ""
% 27.57/3.98  --include_path                          ""
% 27.57/3.98  --clausifier                            res/vclausify_rel
% 27.57/3.98  --clausifier_options                    ""
% 27.57/3.98  --stdin                                 false
% 27.57/3.98  --stats_out                             all
% 27.57/3.98  
% 27.57/3.98  ------ General Options
% 27.57/3.98  
% 27.57/3.98  --fof                                   false
% 27.57/3.98  --time_out_real                         305.
% 27.57/3.98  --time_out_virtual                      -1.
% 27.57/3.98  --symbol_type_check                     false
% 27.57/3.98  --clausify_out                          false
% 27.57/3.98  --sig_cnt_out                           false
% 27.57/3.98  --trig_cnt_out                          false
% 27.57/3.98  --trig_cnt_out_tolerance                1.
% 27.57/3.98  --trig_cnt_out_sk_spl                   false
% 27.57/3.98  --abstr_cl_out                          false
% 27.57/3.98  
% 27.57/3.98  ------ Global Options
% 27.57/3.98  
% 27.57/3.98  --schedule                              default
% 27.57/3.98  --add_important_lit                     false
% 27.57/3.98  --prop_solver_per_cl                    1000
% 27.57/3.98  --min_unsat_core                        false
% 27.57/3.98  --soft_assumptions                      false
% 27.57/3.98  --soft_lemma_size                       3
% 27.57/3.98  --prop_impl_unit_size                   0
% 27.57/3.98  --prop_impl_unit                        []
% 27.57/3.98  --share_sel_clauses                     true
% 27.57/3.98  --reset_solvers                         false
% 27.57/3.98  --bc_imp_inh                            [conj_cone]
% 27.57/3.98  --conj_cone_tolerance                   3.
% 27.57/3.98  --extra_neg_conj                        none
% 27.57/3.98  --large_theory_mode                     true
% 27.57/3.98  --prolific_symb_bound                   200
% 27.57/3.98  --lt_threshold                          2000
% 27.57/3.98  --clause_weak_htbl                      true
% 27.57/3.98  --gc_record_bc_elim                     false
% 27.57/3.98  
% 27.57/3.98  ------ Preprocessing Options
% 27.57/3.98  
% 27.57/3.98  --preprocessing_flag                    true
% 27.57/3.98  --time_out_prep_mult                    0.1
% 27.57/3.98  --splitting_mode                        input
% 27.57/3.98  --splitting_grd                         true
% 27.57/3.98  --splitting_cvd                         false
% 27.57/3.98  --splitting_cvd_svl                     false
% 27.57/3.98  --splitting_nvd                         32
% 27.57/3.98  --sub_typing                            true
% 27.57/3.98  --prep_gs_sim                           true
% 27.57/3.98  --prep_unflatten                        true
% 27.57/3.98  --prep_res_sim                          true
% 27.57/3.98  --prep_upred                            true
% 27.57/3.98  --prep_sem_filter                       exhaustive
% 27.57/3.98  --prep_sem_filter_out                   false
% 27.57/3.98  --pred_elim                             true
% 27.57/3.98  --res_sim_input                         true
% 27.57/3.98  --eq_ax_congr_red                       true
% 27.57/3.98  --pure_diseq_elim                       true
% 27.57/3.98  --brand_transform                       false
% 27.57/3.98  --non_eq_to_eq                          false
% 27.57/3.98  --prep_def_merge                        true
% 27.57/3.98  --prep_def_merge_prop_impl              false
% 27.57/3.98  --prep_def_merge_mbd                    true
% 27.57/3.98  --prep_def_merge_tr_red                 false
% 27.57/3.98  --prep_def_merge_tr_cl                  false
% 27.57/3.98  --smt_preprocessing                     true
% 27.57/3.98  --smt_ac_axioms                         fast
% 27.57/3.98  --preprocessed_out                      false
% 27.57/3.98  --preprocessed_stats                    false
% 27.57/3.98  
% 27.57/3.98  ------ Abstraction refinement Options
% 27.57/3.98  
% 27.57/3.98  --abstr_ref                             []
% 27.57/3.98  --abstr_ref_prep                        false
% 27.57/3.98  --abstr_ref_until_sat                   false
% 27.57/3.98  --abstr_ref_sig_restrict                funpre
% 27.57/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.57/3.98  --abstr_ref_under                       []
% 27.57/3.98  
% 27.57/3.98  ------ SAT Options
% 27.57/3.98  
% 27.57/3.98  --sat_mode                              false
% 27.57/3.98  --sat_fm_restart_options                ""
% 27.57/3.98  --sat_gr_def                            false
% 27.57/3.98  --sat_epr_types                         true
% 27.57/3.98  --sat_non_cyclic_types                  false
% 27.57/3.98  --sat_finite_models                     false
% 27.57/3.98  --sat_fm_lemmas                         false
% 27.57/3.98  --sat_fm_prep                           false
% 27.57/3.98  --sat_fm_uc_incr                        true
% 27.57/3.98  --sat_out_model                         small
% 27.57/3.98  --sat_out_clauses                       false
% 27.57/3.98  
% 27.57/3.98  ------ QBF Options
% 27.57/3.98  
% 27.57/3.98  --qbf_mode                              false
% 27.57/3.98  --qbf_elim_univ                         false
% 27.57/3.98  --qbf_dom_inst                          none
% 27.57/3.98  --qbf_dom_pre_inst                      false
% 27.57/3.98  --qbf_sk_in                             false
% 27.57/3.98  --qbf_pred_elim                         true
% 27.57/3.98  --qbf_split                             512
% 27.57/3.98  
% 27.57/3.98  ------ BMC1 Options
% 27.57/3.98  
% 27.57/3.98  --bmc1_incremental                      false
% 27.57/3.98  --bmc1_axioms                           reachable_all
% 27.57/3.98  --bmc1_min_bound                        0
% 27.57/3.98  --bmc1_max_bound                        -1
% 27.57/3.98  --bmc1_max_bound_default                -1
% 27.57/3.98  --bmc1_symbol_reachability              true
% 27.57/3.98  --bmc1_property_lemmas                  false
% 27.57/3.98  --bmc1_k_induction                      false
% 27.57/3.98  --bmc1_non_equiv_states                 false
% 27.57/3.98  --bmc1_deadlock                         false
% 27.57/3.98  --bmc1_ucm                              false
% 27.57/3.98  --bmc1_add_unsat_core                   none
% 27.57/3.98  --bmc1_unsat_core_children              false
% 27.57/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.57/3.98  --bmc1_out_stat                         full
% 27.57/3.98  --bmc1_ground_init                      false
% 27.57/3.98  --bmc1_pre_inst_next_state              false
% 27.57/3.98  --bmc1_pre_inst_state                   false
% 27.57/3.98  --bmc1_pre_inst_reach_state             false
% 27.57/3.98  --bmc1_out_unsat_core                   false
% 27.57/3.98  --bmc1_aig_witness_out                  false
% 27.57/3.98  --bmc1_verbose                          false
% 27.57/3.98  --bmc1_dump_clauses_tptp                false
% 27.57/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.57/3.98  --bmc1_dump_file                        -
% 27.57/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.57/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.57/3.98  --bmc1_ucm_extend_mode                  1
% 27.57/3.98  --bmc1_ucm_init_mode                    2
% 27.57/3.98  --bmc1_ucm_cone_mode                    none
% 27.57/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.57/3.98  --bmc1_ucm_relax_model                  4
% 27.57/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.57/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.57/3.98  --bmc1_ucm_layered_model                none
% 27.57/3.98  --bmc1_ucm_max_lemma_size               10
% 27.57/3.98  
% 27.57/3.98  ------ AIG Options
% 27.57/3.98  
% 27.57/3.98  --aig_mode                              false
% 27.57/3.98  
% 27.57/3.98  ------ Instantiation Options
% 27.57/3.98  
% 27.57/3.98  --instantiation_flag                    true
% 27.57/3.98  --inst_sos_flag                         true
% 27.57/3.98  --inst_sos_phase                        true
% 27.57/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.57/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.57/3.98  --inst_lit_sel_side                     num_symb
% 27.57/3.98  --inst_solver_per_active                1400
% 27.57/3.98  --inst_solver_calls_frac                1.
% 27.57/3.98  --inst_passive_queue_type               priority_queues
% 27.57/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.57/3.98  --inst_passive_queues_freq              [25;2]
% 27.57/3.98  --inst_dismatching                      true
% 27.57/3.98  --inst_eager_unprocessed_to_passive     true
% 27.57/3.98  --inst_prop_sim_given                   true
% 27.57/3.98  --inst_prop_sim_new                     false
% 27.57/3.98  --inst_subs_new                         false
% 27.57/3.98  --inst_eq_res_simp                      false
% 27.57/3.98  --inst_subs_given                       false
% 27.57/3.98  --inst_orphan_elimination               true
% 27.57/3.98  --inst_learning_loop_flag               true
% 27.57/3.98  --inst_learning_start                   3000
% 27.57/3.98  --inst_learning_factor                  2
% 27.57/3.98  --inst_start_prop_sim_after_learn       3
% 27.57/3.98  --inst_sel_renew                        solver
% 27.57/3.98  --inst_lit_activity_flag                true
% 27.57/3.98  --inst_restr_to_given                   false
% 27.57/3.98  --inst_activity_threshold               500
% 27.57/3.98  --inst_out_proof                        true
% 27.57/3.98  
% 27.57/3.98  ------ Resolution Options
% 27.57/3.98  
% 27.57/3.98  --resolution_flag                       true
% 27.57/3.98  --res_lit_sel                           adaptive
% 27.57/3.98  --res_lit_sel_side                      none
% 27.57/3.98  --res_ordering                          kbo
% 27.57/3.98  --res_to_prop_solver                    active
% 27.57/3.98  --res_prop_simpl_new                    false
% 27.57/3.98  --res_prop_simpl_given                  true
% 27.57/3.98  --res_passive_queue_type                priority_queues
% 27.57/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.57/3.98  --res_passive_queues_freq               [15;5]
% 27.57/3.98  --res_forward_subs                      full
% 27.57/3.98  --res_backward_subs                     full
% 27.57/3.98  --res_forward_subs_resolution           true
% 27.57/3.98  --res_backward_subs_resolution          true
% 27.57/3.98  --res_orphan_elimination                true
% 27.57/3.98  --res_time_limit                        2.
% 27.57/3.98  --res_out_proof                         true
% 27.57/3.98  
% 27.57/3.98  ------ Superposition Options
% 27.57/3.98  
% 27.57/3.98  --superposition_flag                    true
% 27.57/3.98  --sup_passive_queue_type                priority_queues
% 27.57/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.57/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.57/3.98  --demod_completeness_check              fast
% 27.57/3.98  --demod_use_ground                      true
% 27.57/3.98  --sup_to_prop_solver                    passive
% 27.57/3.98  --sup_prop_simpl_new                    true
% 27.57/3.98  --sup_prop_simpl_given                  true
% 27.57/3.98  --sup_fun_splitting                     true
% 27.57/3.98  --sup_smt_interval                      50000
% 27.57/3.98  
% 27.57/3.98  ------ Superposition Simplification Setup
% 27.57/3.98  
% 27.57/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.57/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.57/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.57/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.57/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.57/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.57/3.98  --sup_immed_triv                        [TrivRules]
% 27.57/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_immed_bw_main                     []
% 27.57/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.57/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.57/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_input_bw                          []
% 27.57/3.98  
% 27.57/3.98  ------ Combination Options
% 27.57/3.98  
% 27.57/3.98  --comb_res_mult                         3
% 27.57/3.98  --comb_sup_mult                         2
% 27.57/3.98  --comb_inst_mult                        10
% 27.57/3.98  
% 27.57/3.98  ------ Debug Options
% 27.57/3.98  
% 27.57/3.98  --dbg_backtrace                         false
% 27.57/3.98  --dbg_dump_prop_clauses                 false
% 27.57/3.98  --dbg_dump_prop_clauses_file            -
% 27.57/3.98  --dbg_out_stat                          false
% 27.57/3.98  ------ Parsing...
% 27.57/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.57/3.98  
% 27.57/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.57/3.98  
% 27.57/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.57/3.98  
% 27.57/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.57/3.98  ------ Proving...
% 27.57/3.98  ------ Problem Properties 
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  clauses                                 25
% 27.57/3.98  conjectures                             4
% 27.57/3.98  EPR                                     1
% 27.57/3.98  Horn                                    12
% 27.57/3.98  unary                                   3
% 27.57/3.98  binary                                  8
% 27.57/3.98  lits                                    72
% 27.57/3.98  lits eq                                 16
% 27.57/3.98  fd_pure                                 0
% 27.57/3.98  fd_pseudo                               0
% 27.57/3.98  fd_cond                                 3
% 27.57/3.98  fd_pseudo_cond                          4
% 27.57/3.98  AC symbols                              0
% 27.57/3.98  
% 27.57/3.98  ------ Schedule dynamic 5 is on 
% 27.57/3.98  
% 27.57/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  ------ 
% 27.57/3.98  Current options:
% 27.57/3.98  ------ 
% 27.57/3.98  
% 27.57/3.98  ------ Input Options
% 27.57/3.98  
% 27.57/3.98  --out_options                           all
% 27.57/3.98  --tptp_safe_out                         true
% 27.57/3.98  --problem_path                          ""
% 27.57/3.98  --include_path                          ""
% 27.57/3.98  --clausifier                            res/vclausify_rel
% 27.57/3.98  --clausifier_options                    ""
% 27.57/3.98  --stdin                                 false
% 27.57/3.98  --stats_out                             all
% 27.57/3.98  
% 27.57/3.98  ------ General Options
% 27.57/3.98  
% 27.57/3.98  --fof                                   false
% 27.57/3.98  --time_out_real                         305.
% 27.57/3.98  --time_out_virtual                      -1.
% 27.57/3.98  --symbol_type_check                     false
% 27.57/3.98  --clausify_out                          false
% 27.57/3.98  --sig_cnt_out                           false
% 27.57/3.98  --trig_cnt_out                          false
% 27.57/3.98  --trig_cnt_out_tolerance                1.
% 27.57/3.98  --trig_cnt_out_sk_spl                   false
% 27.57/3.98  --abstr_cl_out                          false
% 27.57/3.98  
% 27.57/3.98  ------ Global Options
% 27.57/3.98  
% 27.57/3.98  --schedule                              default
% 27.57/3.98  --add_important_lit                     false
% 27.57/3.98  --prop_solver_per_cl                    1000
% 27.57/3.98  --min_unsat_core                        false
% 27.57/3.98  --soft_assumptions                      false
% 27.57/3.98  --soft_lemma_size                       3
% 27.57/3.98  --prop_impl_unit_size                   0
% 27.57/3.98  --prop_impl_unit                        []
% 27.57/3.98  --share_sel_clauses                     true
% 27.57/3.98  --reset_solvers                         false
% 27.57/3.98  --bc_imp_inh                            [conj_cone]
% 27.57/3.98  --conj_cone_tolerance                   3.
% 27.57/3.98  --extra_neg_conj                        none
% 27.57/3.98  --large_theory_mode                     true
% 27.57/3.98  --prolific_symb_bound                   200
% 27.57/3.98  --lt_threshold                          2000
% 27.57/3.98  --clause_weak_htbl                      true
% 27.57/3.98  --gc_record_bc_elim                     false
% 27.57/3.98  
% 27.57/3.98  ------ Preprocessing Options
% 27.57/3.98  
% 27.57/3.98  --preprocessing_flag                    true
% 27.57/3.98  --time_out_prep_mult                    0.1
% 27.57/3.98  --splitting_mode                        input
% 27.57/3.98  --splitting_grd                         true
% 27.57/3.98  --splitting_cvd                         false
% 27.57/3.98  --splitting_cvd_svl                     false
% 27.57/3.98  --splitting_nvd                         32
% 27.57/3.98  --sub_typing                            true
% 27.57/3.98  --prep_gs_sim                           true
% 27.57/3.98  --prep_unflatten                        true
% 27.57/3.98  --prep_res_sim                          true
% 27.57/3.98  --prep_upred                            true
% 27.57/3.98  --prep_sem_filter                       exhaustive
% 27.57/3.98  --prep_sem_filter_out                   false
% 27.57/3.98  --pred_elim                             true
% 27.57/3.98  --res_sim_input                         true
% 27.57/3.98  --eq_ax_congr_red                       true
% 27.57/3.98  --pure_diseq_elim                       true
% 27.57/3.98  --brand_transform                       false
% 27.57/3.98  --non_eq_to_eq                          false
% 27.57/3.98  --prep_def_merge                        true
% 27.57/3.98  --prep_def_merge_prop_impl              false
% 27.57/3.98  --prep_def_merge_mbd                    true
% 27.57/3.98  --prep_def_merge_tr_red                 false
% 27.57/3.98  --prep_def_merge_tr_cl                  false
% 27.57/3.98  --smt_preprocessing                     true
% 27.57/3.98  --smt_ac_axioms                         fast
% 27.57/3.98  --preprocessed_out                      false
% 27.57/3.98  --preprocessed_stats                    false
% 27.57/3.98  
% 27.57/3.98  ------ Abstraction refinement Options
% 27.57/3.98  
% 27.57/3.98  --abstr_ref                             []
% 27.57/3.98  --abstr_ref_prep                        false
% 27.57/3.98  --abstr_ref_until_sat                   false
% 27.57/3.98  --abstr_ref_sig_restrict                funpre
% 27.57/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.57/3.98  --abstr_ref_under                       []
% 27.57/3.98  
% 27.57/3.98  ------ SAT Options
% 27.57/3.98  
% 27.57/3.98  --sat_mode                              false
% 27.57/3.98  --sat_fm_restart_options                ""
% 27.57/3.98  --sat_gr_def                            false
% 27.57/3.98  --sat_epr_types                         true
% 27.57/3.98  --sat_non_cyclic_types                  false
% 27.57/3.98  --sat_finite_models                     false
% 27.57/3.98  --sat_fm_lemmas                         false
% 27.57/3.98  --sat_fm_prep                           false
% 27.57/3.98  --sat_fm_uc_incr                        true
% 27.57/3.98  --sat_out_model                         small
% 27.57/3.98  --sat_out_clauses                       false
% 27.57/3.98  
% 27.57/3.98  ------ QBF Options
% 27.57/3.98  
% 27.57/3.98  --qbf_mode                              false
% 27.57/3.98  --qbf_elim_univ                         false
% 27.57/3.98  --qbf_dom_inst                          none
% 27.57/3.98  --qbf_dom_pre_inst                      false
% 27.57/3.98  --qbf_sk_in                             false
% 27.57/3.98  --qbf_pred_elim                         true
% 27.57/3.98  --qbf_split                             512
% 27.57/3.98  
% 27.57/3.98  ------ BMC1 Options
% 27.57/3.98  
% 27.57/3.98  --bmc1_incremental                      false
% 27.57/3.98  --bmc1_axioms                           reachable_all
% 27.57/3.98  --bmc1_min_bound                        0
% 27.57/3.98  --bmc1_max_bound                        -1
% 27.57/3.98  --bmc1_max_bound_default                -1
% 27.57/3.98  --bmc1_symbol_reachability              true
% 27.57/3.98  --bmc1_property_lemmas                  false
% 27.57/3.98  --bmc1_k_induction                      false
% 27.57/3.98  --bmc1_non_equiv_states                 false
% 27.57/3.98  --bmc1_deadlock                         false
% 27.57/3.98  --bmc1_ucm                              false
% 27.57/3.98  --bmc1_add_unsat_core                   none
% 27.57/3.98  --bmc1_unsat_core_children              false
% 27.57/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.57/3.98  --bmc1_out_stat                         full
% 27.57/3.98  --bmc1_ground_init                      false
% 27.57/3.98  --bmc1_pre_inst_next_state              false
% 27.57/3.98  --bmc1_pre_inst_state                   false
% 27.57/3.98  --bmc1_pre_inst_reach_state             false
% 27.57/3.98  --bmc1_out_unsat_core                   false
% 27.57/3.98  --bmc1_aig_witness_out                  false
% 27.57/3.98  --bmc1_verbose                          false
% 27.57/3.98  --bmc1_dump_clauses_tptp                false
% 27.57/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.57/3.98  --bmc1_dump_file                        -
% 27.57/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.57/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.57/3.98  --bmc1_ucm_extend_mode                  1
% 27.57/3.98  --bmc1_ucm_init_mode                    2
% 27.57/3.98  --bmc1_ucm_cone_mode                    none
% 27.57/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.57/3.98  --bmc1_ucm_relax_model                  4
% 27.57/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.57/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.57/3.98  --bmc1_ucm_layered_model                none
% 27.57/3.98  --bmc1_ucm_max_lemma_size               10
% 27.57/3.98  
% 27.57/3.98  ------ AIG Options
% 27.57/3.98  
% 27.57/3.98  --aig_mode                              false
% 27.57/3.98  
% 27.57/3.98  ------ Instantiation Options
% 27.57/3.98  
% 27.57/3.98  --instantiation_flag                    true
% 27.57/3.98  --inst_sos_flag                         true
% 27.57/3.98  --inst_sos_phase                        true
% 27.57/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.57/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.57/3.98  --inst_lit_sel_side                     none
% 27.57/3.98  --inst_solver_per_active                1400
% 27.57/3.98  --inst_solver_calls_frac                1.
% 27.57/3.98  --inst_passive_queue_type               priority_queues
% 27.57/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.57/3.98  --inst_passive_queues_freq              [25;2]
% 27.57/3.98  --inst_dismatching                      true
% 27.57/3.98  --inst_eager_unprocessed_to_passive     true
% 27.57/3.98  --inst_prop_sim_given                   true
% 27.57/3.98  --inst_prop_sim_new                     false
% 27.57/3.98  --inst_subs_new                         false
% 27.57/3.98  --inst_eq_res_simp                      false
% 27.57/3.98  --inst_subs_given                       false
% 27.57/3.98  --inst_orphan_elimination               true
% 27.57/3.98  --inst_learning_loop_flag               true
% 27.57/3.98  --inst_learning_start                   3000
% 27.57/3.98  --inst_learning_factor                  2
% 27.57/3.98  --inst_start_prop_sim_after_learn       3
% 27.57/3.98  --inst_sel_renew                        solver
% 27.57/3.98  --inst_lit_activity_flag                true
% 27.57/3.98  --inst_restr_to_given                   false
% 27.57/3.98  --inst_activity_threshold               500
% 27.57/3.98  --inst_out_proof                        true
% 27.57/3.98  
% 27.57/3.98  ------ Resolution Options
% 27.57/3.98  
% 27.57/3.98  --resolution_flag                       false
% 27.57/3.98  --res_lit_sel                           adaptive
% 27.57/3.98  --res_lit_sel_side                      none
% 27.57/3.98  --res_ordering                          kbo
% 27.57/3.98  --res_to_prop_solver                    active
% 27.57/3.98  --res_prop_simpl_new                    false
% 27.57/3.98  --res_prop_simpl_given                  true
% 27.57/3.98  --res_passive_queue_type                priority_queues
% 27.57/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.57/3.98  --res_passive_queues_freq               [15;5]
% 27.57/3.98  --res_forward_subs                      full
% 27.57/3.98  --res_backward_subs                     full
% 27.57/3.98  --res_forward_subs_resolution           true
% 27.57/3.98  --res_backward_subs_resolution          true
% 27.57/3.98  --res_orphan_elimination                true
% 27.57/3.98  --res_time_limit                        2.
% 27.57/3.98  --res_out_proof                         true
% 27.57/3.98  
% 27.57/3.98  ------ Superposition Options
% 27.57/3.98  
% 27.57/3.98  --superposition_flag                    true
% 27.57/3.98  --sup_passive_queue_type                priority_queues
% 27.57/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.57/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.57/3.98  --demod_completeness_check              fast
% 27.57/3.98  --demod_use_ground                      true
% 27.57/3.98  --sup_to_prop_solver                    passive
% 27.57/3.98  --sup_prop_simpl_new                    true
% 27.57/3.98  --sup_prop_simpl_given                  true
% 27.57/3.98  --sup_fun_splitting                     true
% 27.57/3.98  --sup_smt_interval                      50000
% 27.57/3.98  
% 27.57/3.98  ------ Superposition Simplification Setup
% 27.57/3.98  
% 27.57/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.57/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.57/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.57/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.57/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.57/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.57/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.57/3.98  --sup_immed_triv                        [TrivRules]
% 27.57/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_immed_bw_main                     []
% 27.57/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.57/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.57/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.57/3.98  --sup_input_bw                          []
% 27.57/3.98  
% 27.57/3.98  ------ Combination Options
% 27.57/3.98  
% 27.57/3.98  --comb_res_mult                         3
% 27.57/3.98  --comb_sup_mult                         2
% 27.57/3.98  --comb_inst_mult                        10
% 27.57/3.98  
% 27.57/3.98  ------ Debug Options
% 27.57/3.98  
% 27.57/3.98  --dbg_backtrace                         false
% 27.57/3.98  --dbg_dump_prop_clauses                 false
% 27.57/3.98  --dbg_dump_prop_clauses_file            -
% 27.57/3.98  --dbg_out_stat                          false
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  ------ Proving...
% 27.57/3.98  
% 27.57/3.98  
% 27.57/3.98  % SZS status Theorem for theBenchmark.p
% 27.57/3.98  
% 27.57/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.57/3.98  
% 27.57/3.98  fof(f8,axiom,(
% 27.57/3.98    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f11,plain,(
% 27.57/3.98    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 27.57/3.98    inference(rectify,[],[f8])).
% 27.57/3.98  
% 27.57/3.98  fof(f21,plain,(
% 27.57/3.98    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(ennf_transformation,[],[f11])).
% 27.57/3.98  
% 27.57/3.98  fof(f22,plain,(
% 27.57/3.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(flattening,[],[f21])).
% 27.57/3.98  
% 27.57/3.98  fof(f48,plain,(
% 27.57/3.98    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(nnf_transformation,[],[f22])).
% 27.57/3.98  
% 27.57/3.98  fof(f49,plain,(
% 27.57/3.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(flattening,[],[f48])).
% 27.57/3.98  
% 27.57/3.98  fof(f50,plain,(
% 27.57/3.98    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(rectify,[],[f49])).
% 27.57/3.98  
% 27.57/3.98  fof(f53,plain,(
% 27.57/3.98    ( ! [X3] : (! [X1,X0] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) => (~r2_hidden(sK10(X0,X1),X0) & r2_hidden(k4_tarski(sK10(X0,X1),X3),X1)))) )),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f52,plain,(
% 27.57/3.98    ! [X1,X0] : (? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0)) => (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0)))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f51,plain,(
% 27.57/3.98    ! [X1,X0] : (? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) => (k1_wellord1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k3_relat_1(X1))))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f54,plain,(
% 27.57/3.98    ! [X0,X1] : ((((k1_wellord1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ((~r2_hidden(sK10(X0,X1),X0) & r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f50,f53,f52,f51])).
% 27.57/3.98  
% 27.57/3.98  fof(f90,plain,(
% 27.57/3.98    ( ! [X6,X0,X7,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,X0) | k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f54])).
% 27.57/3.98  
% 27.57/3.98  fof(f107,plain,(
% 27.57/3.98    ( ! [X6,X7,X5,X1] : (r2_hidden(X6,k1_wellord1(X1,X7)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,k1_wellord1(X1,X7)) | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 27.57/3.98    inference(equality_resolution,[],[f90])).
% 27.57/3.98  
% 27.57/3.98  fof(f9,conjecture,(
% 27.57/3.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f10,negated_conjecture,(
% 27.57/3.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 27.57/3.98    inference(negated_conjecture,[],[f9])).
% 27.57/3.98  
% 27.57/3.98  fof(f23,plain,(
% 27.57/3.98    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 27.57/3.98    inference(ennf_transformation,[],[f10])).
% 27.57/3.98  
% 27.57/3.98  fof(f24,plain,(
% 27.57/3.98    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 27.57/3.98    inference(flattening,[],[f23])).
% 27.57/3.98  
% 27.57/3.98  fof(f55,plain,(
% 27.57/3.98    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 27.57/3.98    inference(nnf_transformation,[],[f24])).
% 27.57/3.98  
% 27.57/3.98  fof(f56,plain,(
% 27.57/3.98    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 27.57/3.98    inference(flattening,[],[f55])).
% 27.57/3.98  
% 27.57/3.98  fof(f57,plain,(
% 27.57/3.98    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | ~r2_hidden(k4_tarski(sK11,sK12),sK13)) & (r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | r2_hidden(k4_tarski(sK11,sK12),sK13)) & r2_hidden(sK12,k3_relat_1(sK13)) & r2_hidden(sK11,k3_relat_1(sK13)) & v2_wellord1(sK13) & v1_relat_1(sK13))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f58,plain,(
% 27.57/3.98    (~r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | ~r2_hidden(k4_tarski(sK11,sK12),sK13)) & (r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | r2_hidden(k4_tarski(sK11,sK12),sK13)) & r2_hidden(sK12,k3_relat_1(sK13)) & r2_hidden(sK11,k3_relat_1(sK13)) & v2_wellord1(sK13) & v1_relat_1(sK13)),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f56,f57])).
% 27.57/3.98  
% 27.57/3.98  fof(f98,plain,(
% 27.57/3.98    v2_wellord1(sK13)),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f97,plain,(
% 27.57/3.98    v1_relat_1(sK13)),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f2,axiom,(
% 27.57/3.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f13,plain,(
% 27.57/3.98    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 27.57/3.98    inference(ennf_transformation,[],[f2])).
% 27.57/3.98  
% 27.57/3.98  fof(f14,plain,(
% 27.57/3.98    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 27.57/3.98    inference(flattening,[],[f13])).
% 27.57/3.98  
% 27.57/3.98  fof(f62,plain,(
% 27.57/3.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f14])).
% 27.57/3.98  
% 27.57/3.98  fof(f101,plain,(
% 27.57/3.98    r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | r2_hidden(k4_tarski(sK11,sK12),sK13)),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f7,axiom,(
% 27.57/3.98    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f20,plain,(
% 27.57/3.98    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(ennf_transformation,[],[f7])).
% 27.57/3.98  
% 27.57/3.98  fof(f44,plain,(
% 27.57/3.98    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(nnf_transformation,[],[f20])).
% 27.57/3.98  
% 27.57/3.98  fof(f45,plain,(
% 27.57/3.98    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(rectify,[],[f44])).
% 27.57/3.98  
% 27.57/3.98  fof(f46,plain,(
% 27.57/3.98    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0))))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f47,plain,(
% 27.57/3.98    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f45,f46])).
% 27.57/3.98  
% 27.57/3.98  fof(f83,plain,(
% 27.57/3.98    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f47])).
% 27.57/3.98  
% 27.57/3.98  fof(f4,axiom,(
% 27.57/3.98    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f16,plain,(
% 27.57/3.98    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(ennf_transformation,[],[f4])).
% 27.57/3.98  
% 27.57/3.98  fof(f34,plain,(
% 27.57/3.98    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(nnf_transformation,[],[f16])).
% 27.57/3.98  
% 27.57/3.98  fof(f35,plain,(
% 27.57/3.98    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(flattening,[],[f34])).
% 27.57/3.98  
% 27.57/3.98  fof(f73,plain,(
% 27.57/3.98    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f35])).
% 27.57/3.98  
% 27.57/3.98  fof(f3,axiom,(
% 27.57/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f15,plain,(
% 27.57/3.98    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(ennf_transformation,[],[f3])).
% 27.57/3.98  
% 27.57/3.98  fof(f29,plain,(
% 27.57/3.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(nnf_transformation,[],[f15])).
% 27.57/3.98  
% 27.57/3.98  fof(f30,plain,(
% 27.57/3.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(flattening,[],[f29])).
% 27.57/3.98  
% 27.57/3.98  fof(f31,plain,(
% 27.57/3.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(rectify,[],[f30])).
% 27.57/3.98  
% 27.57/3.98  fof(f32,plain,(
% 27.57/3.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f33,plain,(
% 27.57/3.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 27.57/3.98  
% 27.57/3.98  fof(f66,plain,(
% 27.57/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f33])).
% 27.57/3.98  
% 27.57/3.98  fof(f103,plain,(
% 27.57/3.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(equality_resolution,[],[f66])).
% 27.57/3.98  
% 27.57/3.98  fof(f1,axiom,(
% 27.57/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f12,plain,(
% 27.57/3.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.57/3.98    inference(ennf_transformation,[],[f1])).
% 27.57/3.98  
% 27.57/3.98  fof(f25,plain,(
% 27.57/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.57/3.98    inference(nnf_transformation,[],[f12])).
% 27.57/3.98  
% 27.57/3.98  fof(f26,plain,(
% 27.57/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.57/3.98    inference(rectify,[],[f25])).
% 27.57/3.98  
% 27.57/3.98  fof(f27,plain,(
% 27.57/3.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f28,plain,(
% 27.57/3.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 27.57/3.98  
% 27.57/3.98  fof(f60,plain,(
% 27.57/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f28])).
% 27.57/3.98  
% 27.57/3.98  fof(f65,plain,(
% 27.57/3.98    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f33])).
% 27.57/3.98  
% 27.57/3.98  fof(f104,plain,(
% 27.57/3.98    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(equality_resolution,[],[f65])).
% 27.57/3.98  
% 27.57/3.98  fof(f6,axiom,(
% 27.57/3.98    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f18,plain,(
% 27.57/3.98    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(ennf_transformation,[],[f6])).
% 27.57/3.98  
% 27.57/3.98  fof(f19,plain,(
% 27.57/3.98    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(flattening,[],[f18])).
% 27.57/3.98  
% 27.57/3.98  fof(f40,plain,(
% 27.57/3.98    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(nnf_transformation,[],[f19])).
% 27.57/3.98  
% 27.57/3.98  fof(f41,plain,(
% 27.57/3.98    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(rectify,[],[f40])).
% 27.57/3.98  
% 27.57/3.98  fof(f42,plain,(
% 27.57/3.98    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f43,plain,(
% 27.57/3.98    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK3(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).
% 27.57/3.98  
% 27.57/3.98  fof(f79,plain,(
% 27.57/3.98    ( ! [X6,X4,X0,X5] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f43])).
% 27.57/3.98  
% 27.57/3.98  fof(f71,plain,(
% 27.57/3.98    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f35])).
% 27.57/3.98  
% 27.57/3.98  fof(f61,plain,(
% 27.57/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f28])).
% 27.57/3.98  
% 27.57/3.98  fof(f102,plain,(
% 27.57/3.98    ~r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) | ~r2_hidden(k4_tarski(sK11,sK12),sK13)),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f99,plain,(
% 27.57/3.98    r2_hidden(sK11,k3_relat_1(sK13))),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f100,plain,(
% 27.57/3.98    r2_hidden(sK12,k3_relat_1(sK13))),
% 27.57/3.98    inference(cnf_transformation,[],[f58])).
% 27.57/3.98  
% 27.57/3.98  fof(f5,axiom,(
% 27.57/3.98    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 27.57/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.57/3.98  
% 27.57/3.98  fof(f17,plain,(
% 27.57/3.98    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(ennf_transformation,[],[f5])).
% 27.57/3.98  
% 27.57/3.98  fof(f36,plain,(
% 27.57/3.98    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(nnf_transformation,[],[f17])).
% 27.57/3.98  
% 27.57/3.98  fof(f37,plain,(
% 27.57/3.98    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(rectify,[],[f36])).
% 27.57/3.98  
% 27.57/3.98  fof(f38,plain,(
% 27.57/3.98    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 27.57/3.98    introduced(choice_axiom,[])).
% 27.57/3.98  
% 27.57/3.98  fof(f39,plain,(
% 27.57/3.98    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 27.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 27.57/3.98  
% 27.57/3.98  fof(f76,plain,(
% 27.57/3.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f39])).
% 27.57/3.98  
% 27.57/3.98  fof(f70,plain,(
% 27.57/3.98    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f35])).
% 27.57/3.98  
% 27.57/3.98  fof(f59,plain,(
% 27.57/3.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f28])).
% 27.57/3.98  
% 27.57/3.98  fof(f64,plain,(
% 27.57/3.98    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(cnf_transformation,[],[f33])).
% 27.57/3.98  
% 27.57/3.98  fof(f105,plain,(
% 27.57/3.98    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(equality_resolution,[],[f64])).
% 27.57/3.98  
% 27.57/3.98  fof(f106,plain,(
% 27.57/3.98    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 27.57/3.98    inference(equality_resolution,[],[f105])).
% 27.57/3.98  
% 27.57/3.98  cnf(c_36,plain,
% 27.57/3.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | r2_hidden(X3,k1_wellord1(X1,X2))
% 27.57/3.99      | ~ r2_hidden(X2,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 27.57/3.99      | ~ v2_wellord1(X1)
% 27.57/3.99      | ~ v1_relat_1(X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f107]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_42,negated_conjecture,
% 27.57/3.99      ( v2_wellord1(sK13) ),
% 27.57/3.99      inference(cnf_transformation,[],[f98]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_757,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | r2_hidden(X3,k1_wellord1(X1,X2))
% 27.57/3.99      | ~ r2_hidden(X2,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_36,c_42]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_758,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
% 27.57/3.99      | r2_hidden(X2,k1_wellord1(sK13,X1))
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X2,X0),sK13)
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13))
% 27.57/3.99      | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_757]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_43,negated_conjecture,
% 27.57/3.99      ( v1_relat_1(sK13) ),
% 27.57/3.99      inference(cnf_transformation,[],[f97]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_760,plain,
% 27.57/3.99      ( ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X2,X0),sK13)
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(X2,k1_wellord1(sK13,X1))
% 27.57/3.99      | ~ r2_hidden(X0,k1_wellord1(sK13,X1)) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_758,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_761,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
% 27.57/3.99      | r2_hidden(X2,k1_wellord1(sK13,X1))
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X2,X0),sK13)
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,X1),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_760]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_95486,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,sK11))
% 27.57/3.99      | r2_hidden(X1,k1_wellord1(sK13,sK11))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X0),sK13)
% 27.57/3.99      | ~ r2_hidden(sK11,k3_relat_1(sK13))
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_761]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_96099,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,sK11))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(sK11,X0),sK13)
% 27.57/3.99      | r2_hidden(sK11,k1_wellord1(sK13,sK11))
% 27.57/3.99      | ~ r2_hidden(sK11,k3_relat_1(sK13))
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_95486]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_98356,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | ~ r2_hidden(sK12,k1_wellord1(sK13,sK11))
% 27.57/3.99      | r2_hidden(sK11,k1_wellord1(sK13,sK11))
% 27.57/3.99      | ~ r2_hidden(sK11,k3_relat_1(sK13))
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_96099]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4,plain,
% 27.57/3.99      ( r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v1_relat_1(X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1377,plain,
% 27.57/3.99      ( r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_4,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1378,plain,
% 27.57/3.99      ( r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1377]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_48638,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK0(X0,k3_relat_1(sK13)),X1),sK13)
% 27.57/3.99      | r2_hidden(sK0(X0,k3_relat_1(sK13)),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_71036,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),sK11),sK13)
% 27.57/3.99      | r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_48638]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_39,negated_conjecture,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f101]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3405,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_29,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(X2,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v6_relat_2(X1)
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | X0 = X2 ),
% 27.57/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1306,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(X2,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v6_relat_2(X1)
% 27.57/3.99      | X2 = X0
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_29,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1307,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13)
% 27.57/3.99      | ~ v6_relat_2(sK13)
% 27.57/3.99      | X0 = X1 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1306]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_13,plain,
% 27.57/3.99      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_746,plain,
% 27.57/3.99      ( v6_relat_2(X0) | ~ v1_relat_1(X0) | sK13 != X0 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_13,c_42]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_747,plain,
% 27.57/3.99      ( v6_relat_2(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_746]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_117,plain,
% 27.57/3.99      ( v6_relat_2(sK13) | ~ v2_wellord1(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_13]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_749,plain,
% 27.57/3.99      ( v6_relat_2(sK13) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_747,c_43,c_42,c_117]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1243,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | ~ r2_hidden(X2,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | X2 = X0
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_29,c_749]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1244,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13)
% 27.57/3.99      | ~ v1_relat_1(sK13)
% 27.57/3.99      | X0 = X1 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1243]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1309,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X1,X0),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | X0 = X1 ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_1307,c_43,c_1244]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1310,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(X1,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | X1 = X0 ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_1309]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3393,plain,
% 27.57/3.99      ( X0 = X1
% 27.57/3.99      | r2_hidden(X0,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(X1,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_8,plain,
% 27.57/3.99      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | X0 = X2 ),
% 27.57/3.99      inference(cnf_transformation,[],[f103]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1362,plain,
% 27.57/3.99      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | X2 = X0
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_8,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1363,plain,
% 27.57/3.99      ( r2_hidden(X0,k1_wellord1(sK13,X1))
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | X1 = X0 ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1362]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3390,plain,
% 27.57/3.99      ( X0 = X1
% 27.57/3.99      | r2_hidden(X1,k1_wellord1(sK13,X0)) = iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5475,plain,
% 27.57/3.99      ( X0 = X1
% 27.57/3.99      | r2_hidden(X0,k1_wellord1(sK13,X1)) = iProver_top
% 27.57/3.99      | r2_hidden(X0,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(X1,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X0),sK13) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3393,c_3390]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1,plain,
% 27.57/3.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3408,plain,
% 27.57/3.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 27.57/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_9,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | ~ v1_relat_1(X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f104]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1352,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),X1)
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_9,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1353,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1352]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3391,plain,
% 27.57/3.99      ( r2_hidden(X0,k1_wellord1(sK13,X1)) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1353]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4263,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),X1),X0),sK13) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,X0),X1) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3408,c_3391]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 27.57/3.99      | r2_hidden(k4_tarski(X3,X1),X2)
% 27.57/3.99      | ~ v8_relat_2(X2)
% 27.57/3.99      | ~ v1_relat_1(X2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1467,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 27.57/3.99      | r2_hidden(k4_tarski(X3,X1),X2)
% 27.57/3.99      | ~ v8_relat_2(X2)
% 27.57/3.99      | sK13 != X2 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_23,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1468,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13)
% 27.57/3.99      | ~ v8_relat_2(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1467]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_15,plain,
% 27.57/3.99      ( v8_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_735,plain,
% 27.57/3.99      ( v8_relat_2(X0) | ~ v1_relat_1(X0) | sK13 != X0 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_15,c_42]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_736,plain,
% 27.57/3.99      ( v8_relat_2(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_735]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_111,plain,
% 27.57/3.99      ( v8_relat_2(sK13) | ~ v2_wellord1(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_15]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_738,plain,
% 27.57/3.99      ( v8_relat_2(sK13) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_736,c_43,c_42,c_111]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1083,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 27.57/3.99      | r2_hidden(k4_tarski(X3,X1),X2)
% 27.57/3.99      | ~ v1_relat_1(X2)
% 27.57/3.99      | sK13 != X2 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_23,c_738]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1084,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13)
% 27.57/3.99      | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1083]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1086,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X2),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_1084,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1087,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_1086]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1470,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X2),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X0,X1),sK13) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_1468,c_43,c_1084]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1471,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(X1,X2),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_1470]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3394,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X1,X2),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4743,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),X2),X1),sK13) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,X0),X2) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4263,c_3394]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_8244,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,X0),X1) = X2
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X2),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(sK0(k1_wellord1(sK13,X0),X1),k1_wellord1(sK13,X2)) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,X0),X1) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_4743,c_3390]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_0,plain,
% 27.57/3.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f61]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3409,plain,
% 27.57/3.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 27.57/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_22063,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,X0),k1_wellord1(sK13,X1)) = X1
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X1),sK13) != iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,X0),k1_wellord1(sK13,X1)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_8244,c_3409]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_38,negated_conjecture,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | ~ r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f102]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3406,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_22327,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_22063,c_3406]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_22412,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | sK12 = sK11
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top
% 27.57/3.99      | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_5475,c_22327]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_41,negated_conjecture,
% 27.57/3.99      ( r2_hidden(sK11,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f99]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_46,plain,
% 27.57/3.99      ( r2_hidden(sK11,k3_relat_1(sK13)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_40,negated_conjecture,
% 27.57/3.99      ( r2_hidden(sK12,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(cnf_transformation,[],[f100]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_47,plain,
% 27.57/3.99      ( r2_hidden(sK12,k3_relat_1(sK13)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2843,plain,( X0 = X0 ),theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2864,plain,
% 27.57/3.99      ( sK13 = sK13 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2843]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_19,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),X1)
% 27.57/3.99      | ~ v1_relat_2(X1)
% 27.57/3.99      | ~ v1_relat_1(X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1329,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),X1)
% 27.57/3.99      | ~ v1_relat_2(X1)
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_19,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1330,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),sK13)
% 27.57/3.99      | ~ v1_relat_2(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1329]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_16,plain,
% 27.57/3.99      ( v1_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 27.57/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_724,plain,
% 27.57/3.99      ( v1_relat_2(X0) | ~ v1_relat_1(X0) | sK13 != X0 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_16,c_42]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_725,plain,
% 27.57/3.99      ( v1_relat_2(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_724]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_108,plain,
% 27.57/3.99      ( v1_relat_2(sK13) | ~ v2_wellord1(sK13) | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_16]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_727,plain,
% 27.57/3.99      ( v1_relat_2(sK13) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_725,c_43,c_42,c_108]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_998,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),X1)
% 27.57/3.99      | ~ v1_relat_1(X1)
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_19,c_727]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_999,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),sK13)
% 27.57/3.99      | ~ v1_relat_1(sK13) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_998]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1003,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X0),sK13)
% 27.57/3.99      | ~ r2_hidden(X0,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_999,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1004,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),sK13) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_1003]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1332,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(X0,X0),sK13)
% 27.57/3.99      | ~ r2_hidden(X0,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_1330,c_43,c_999]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1333,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,X0),sK13) ),
% 27.57/3.99      inference(renaming,[status(thm)],[c_1332]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3478,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK11),sK13)
% 27.57/3.99      | ~ r2_hidden(sK11,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1333]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3479,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK11),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3478]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2846,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.57/3.99      theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3460,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,X1)
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | k4_tarski(sK11,sK12) != X0
% 27.57/3.99      | sK13 != X1 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2846]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3544,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | ~ r2_hidden(k4_tarski(sK11,sK11),sK13)
% 27.57/3.99      | k4_tarski(sK11,sK12) != k4_tarski(sK11,sK11)
% 27.57/3.99      | sK13 != sK13 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_3460]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3545,plain,
% 27.57/3.99      ( k4_tarski(sK11,sK12) != k4_tarski(sK11,sK11)
% 27.57/3.99      | sK13 != sK13
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK11),sK13) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3544]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2848,plain,
% 27.57/3.99      ( X0 != X1 | X2 != X3 | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
% 27.57/3.99      theory(equality) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3649,plain,
% 27.57/3.99      ( k4_tarski(sK11,sK12) = k4_tarski(sK11,sK11)
% 27.57/3.99      | sK12 != sK11
% 27.57/3.99      | sK11 != sK11 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2848]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4660,plain,
% 27.57/3.99      ( sK11 = sK11 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2843]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23507,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_22412,c_46,c_47,c_2864,c_3479,c_3545,c_3649,c_4660,
% 27.57/3.99                 c_22327]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23513,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,sK11),sK13) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_23507,c_3391]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_2,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 27.57/3.99      inference(cnf_transformation,[],[f59]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3407,plain,
% 27.57/3.99      ( r2_hidden(X0,X1) != iProver_top
% 27.57/3.99      | r2_hidden(X0,X2) = iProver_top
% 27.57/3.99      | r1_tarski(X1,X2) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23608,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,sK11),X0) = iProver_top
% 27.57/3.99      | r1_tarski(sK13,X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_23513,c_3407]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_10,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 27.57/3.99      inference(cnf_transformation,[],[f106]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1343,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | sK13 != X1 ),
% 27.57/3.99      inference(resolution_lifted,[status(thm)],[c_10,c_43]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_1344,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k1_wellord1(sK13,X0)) ),
% 27.57/3.99      inference(unflattening,[status(thm)],[c_1343]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4186,plain,
% 27.57/3.99      ( ~ r2_hidden(sK12,k1_wellord1(sK13,sK12)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1344]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_22357,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
% 27.57/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_22327]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23511,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(sK12,X0) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_23507,c_3407]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23767,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK12)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3405,c_23511]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23777,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK12))
% 27.57/3.99      | sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
% 27.57/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_23767]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23782,plain,
% 27.57/3.99      ( sK0(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = sK12 ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_23608,c_4186,c_22357,c_23777]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23792,plain,
% 27.57/3.99      ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_23782,c_3408]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_49,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13) != iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k1_wellord1(sK13,sK12)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3475,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK12,sK12),sK13)
% 27.57/3.99      | ~ r2_hidden(sK12,k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1333]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3476,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK12,sK12),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3475]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3541,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK12,sK12),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | k4_tarski(sK11,sK12) != k4_tarski(sK12,sK12)
% 27.57/3.99      | sK13 != sK13 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_3460]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3542,plain,
% 27.57/3.99      ( k4_tarski(sK11,sK12) != k4_tarski(sK12,sK12)
% 27.57/3.99      | sK13 != sK13
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,sK12),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_3541]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3640,plain,
% 27.57/3.99      ( k4_tarski(sK11,sK12) = k4_tarski(sK12,sK12)
% 27.57/3.99      | sK12 != sK12
% 27.57/3.99      | sK11 != sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2848]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4656,plain,
% 27.57/3.99      ( sK12 = sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_2843]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3841,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK12,X0),sK13)
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,X0))
% 27.57/3.99      | X0 = sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1363]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5271,plain,
% 27.57/3.99      ( ~ r2_hidden(k4_tarski(sK12,sK11),sK13)
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK11))
% 27.57/3.99      | sK11 = sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_3841]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5273,plain,
% 27.57/3.99      ( sK11 = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,sK11),sK13) != iProver_top
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_5271]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3840,plain,
% 27.57/3.99      ( ~ r2_hidden(X0,k3_relat_1(sK13))
% 27.57/3.99      | r2_hidden(k4_tarski(X0,sK12),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,X0),sK13)
% 27.57/3.99      | ~ r2_hidden(sK12,k3_relat_1(sK13))
% 27.57/3.99      | X0 = sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5504,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK12,sK11),sK13)
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | ~ r2_hidden(sK12,k3_relat_1(sK13))
% 27.57/3.99      | ~ r2_hidden(sK11,k3_relat_1(sK13))
% 27.57/3.99      | sK11 = sK12 ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_3840]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_5505,plain,
% 27.57/3.99      ( sK11 = sK12
% 27.57/3.99      | r2_hidden(k4_tarski(sK12,sK11),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(sK12,k3_relat_1(sK13)) != iProver_top
% 27.57/3.99      | r2_hidden(sK11,k3_relat_1(sK13)) != iProver_top ),
% 27.57/3.99      inference(predicate_to_equality,[status(thm)],[c_5504]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23962,plain,
% 27.57/3.99      ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) = iProver_top ),
% 27.57/3.99      inference(global_propositional_subsumption,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_23792,c_46,c_47,c_49,c_2864,c_3476,c_3542,c_3640,
% 27.57/3.99                 c_4656,c_5273,c_5505]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23966,plain,
% 27.57/3.99      ( r2_hidden(sK12,X0) = iProver_top
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),X0) != iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_23962,c_3407]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23977,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13) = iProver_top
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK12)) = iProver_top ),
% 27.57/3.99      inference(superposition,[status(thm)],[c_3405,c_23966]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23987,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK11,sK12),sK13)
% 27.57/3.99      | r2_hidden(sK12,k1_wellord1(sK13,sK12)) ),
% 27.57/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_23977]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_23964,plain,
% 27.57/3.99      ( r2_hidden(sK12,k1_wellord1(sK13,sK11)) ),
% 27.57/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_23962]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_6047,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,X0),k3_relat_1(sK13)),X0),sK13)
% 27.57/3.99      | ~ r2_hidden(sK0(k1_wellord1(sK13,X0),k3_relat_1(sK13)),k1_wellord1(sK13,X0)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1353]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_10151,plain,
% 27.57/3.99      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),sK11),sK13)
% 27.57/3.99      | ~ r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k1_wellord1(sK13,sK11)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_6047]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_4232,plain,
% 27.57/3.99      ( ~ r2_hidden(sK11,k1_wellord1(sK13,sK11)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1344]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3621,plain,
% 27.57/3.99      ( ~ r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k3_relat_1(sK13))
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(c_3622,plain,
% 27.57/3.99      ( r2_hidden(sK0(k1_wellord1(sK13,sK11),k3_relat_1(sK13)),k1_wellord1(sK13,sK11))
% 27.57/3.99      | r1_tarski(k1_wellord1(sK13,sK11),k3_relat_1(sK13)) ),
% 27.57/3.99      inference(instantiation,[status(thm)],[c_1]) ).
% 27.57/3.99  
% 27.57/3.99  cnf(contradiction,plain,
% 27.57/3.99      ( $false ),
% 27.57/3.99      inference(minisat,
% 27.57/3.99                [status(thm)],
% 27.57/3.99                [c_98356,c_71036,c_23987,c_23964,c_10151,c_4232,c_4186,
% 27.57/3.99                 c_3621,c_3622,c_41]) ).
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.57/3.99  
% 27.57/3.99  ------                               Statistics
% 27.57/3.99  
% 27.57/3.99  ------ General
% 27.57/3.99  
% 27.57/3.99  abstr_ref_over_cycles:                  0
% 27.57/3.99  abstr_ref_under_cycles:                 0
% 27.57/3.99  gc_basic_clause_elim:                   0
% 27.57/3.99  forced_gc_time:                         0
% 27.57/3.99  parsing_time:                           0.008
% 27.57/3.99  unif_index_cands_time:                  0.
% 27.57/3.99  unif_index_add_time:                    0.
% 27.57/3.99  orderings_time:                         0.
% 27.57/3.99  out_proof_time:                         0.015
% 27.57/3.99  total_time:                             3.273
% 27.57/3.99  num_of_symbols:                         57
% 27.57/3.99  num_of_terms:                           62374
% 27.57/3.99  
% 27.57/3.99  ------ Preprocessing
% 27.57/3.99  
% 27.57/3.99  num_of_splits:                          0
% 27.57/3.99  num_of_split_atoms:                     0
% 27.57/3.99  num_of_reused_defs:                     0
% 27.57/3.99  num_eq_ax_congr_red:                    36
% 27.57/3.99  num_of_sem_filtered_clauses:            1
% 27.57/3.99  num_of_subtypes:                        0
% 27.57/3.99  monotx_restored_types:                  0
% 27.57/3.99  sat_num_of_epr_types:                   0
% 27.57/3.99  sat_num_of_non_cyclic_types:            0
% 27.57/3.99  sat_guarded_non_collapsed_types:        0
% 27.57/3.99  num_pure_diseq_elim:                    0
% 27.57/3.99  simp_replaced_by:                       0
% 27.57/3.99  res_preprocessed:                       141
% 27.57/3.99  prep_upred:                             0
% 27.57/3.99  prep_unflattend:                        139
% 27.57/3.99  smt_new_axioms:                         0
% 27.57/3.99  pred_elim_cands:                        2
% 27.57/3.99  pred_elim:                              7
% 27.57/3.99  pred_elim_cl:                           18
% 27.57/3.99  pred_elim_cycles:                       14
% 27.57/3.99  merged_defs:                            8
% 27.57/3.99  merged_defs_ncl:                        0
% 27.57/3.99  bin_hyper_res:                          8
% 27.57/3.99  prep_cycles:                            4
% 27.57/3.99  pred_elim_time:                         0.038
% 27.57/3.99  splitting_time:                         0.
% 27.57/3.99  sem_filter_time:                        0.
% 27.57/3.99  monotx_time:                            0.
% 27.57/3.99  subtype_inf_time:                       0.
% 27.57/3.99  
% 27.57/3.99  ------ Problem properties
% 27.57/3.99  
% 27.57/3.99  clauses:                                25
% 27.57/3.99  conjectures:                            4
% 27.57/3.99  epr:                                    1
% 27.57/3.99  horn:                                   12
% 27.57/3.99  ground:                                 4
% 27.57/3.99  unary:                                  3
% 27.57/3.99  binary:                                 8
% 27.57/3.99  lits:                                   72
% 27.57/3.99  lits_eq:                                16
% 27.57/3.99  fd_pure:                                0
% 27.57/3.99  fd_pseudo:                              0
% 27.57/3.99  fd_cond:                                3
% 27.57/3.99  fd_pseudo_cond:                         4
% 27.57/3.99  ac_symbols:                             0
% 27.57/3.99  
% 27.57/3.99  ------ Propositional Solver
% 27.57/3.99  
% 27.57/3.99  prop_solver_calls:                      37
% 27.57/3.99  prop_fast_solver_calls:                 3726
% 27.57/3.99  smt_solver_calls:                       0
% 27.57/3.99  smt_fast_solver_calls:                  0
% 27.57/3.99  prop_num_of_clauses:                    27500
% 27.57/3.99  prop_preprocess_simplified:             40063
% 27.57/3.99  prop_fo_subsumed:                       76
% 27.57/3.99  prop_solver_time:                       0.
% 27.57/3.99  smt_solver_time:                        0.
% 27.57/3.99  smt_fast_solver_time:                   0.
% 27.57/3.99  prop_fast_solver_time:                  0.
% 27.57/3.99  prop_unsat_core_time:                   0.002
% 27.57/3.99  
% 27.57/3.99  ------ QBF
% 27.57/3.99  
% 27.57/3.99  qbf_q_res:                              0
% 27.57/3.99  qbf_num_tautologies:                    0
% 27.57/3.99  qbf_prep_cycles:                        0
% 27.57/3.99  
% 27.57/3.99  ------ BMC1
% 27.57/3.99  
% 27.57/3.99  bmc1_current_bound:                     -1
% 27.57/3.99  bmc1_last_solved_bound:                 -1
% 27.57/3.99  bmc1_unsat_core_size:                   -1
% 27.57/3.99  bmc1_unsat_core_parents_size:           -1
% 27.57/3.99  bmc1_merge_next_fun:                    0
% 27.57/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.57/3.99  
% 27.57/3.99  ------ Instantiation
% 27.57/3.99  
% 27.57/3.99  inst_num_of_clauses:                    348
% 27.57/3.99  inst_num_in_passive:                    59
% 27.57/3.99  inst_num_in_active:                     2566
% 27.57/3.99  inst_num_in_unprocessed:                139
% 27.57/3.99  inst_num_of_loops:                      3156
% 27.57/3.99  inst_num_of_learning_restarts:          1
% 27.57/3.99  inst_num_moves_active_passive:          585
% 27.57/3.99  inst_lit_activity:                      0
% 27.57/3.99  inst_lit_activity_moves:                1
% 27.57/3.99  inst_num_tautologies:                   0
% 27.57/3.99  inst_num_prop_implied:                  0
% 27.57/3.99  inst_num_existing_simplified:           0
% 27.57/3.99  inst_num_eq_res_simplified:             0
% 27.57/3.99  inst_num_child_elim:                    0
% 27.57/3.99  inst_num_of_dismatching_blockings:      34587
% 27.57/3.99  inst_num_of_non_proper_insts:           10429
% 27.57/3.99  inst_num_of_duplicates:                 0
% 27.57/3.99  inst_inst_num_from_inst_to_res:         0
% 27.57/3.99  inst_dismatching_checking_time:         0.
% 27.57/3.99  
% 27.57/3.99  ------ Resolution
% 27.57/3.99  
% 27.57/3.99  res_num_of_clauses:                     36
% 27.57/3.99  res_num_in_passive:                     36
% 27.57/3.99  res_num_in_active:                      0
% 27.57/3.99  res_num_of_loops:                       145
% 27.57/3.99  res_forward_subset_subsumed:            606
% 27.57/3.99  res_backward_subset_subsumed:           10
% 27.57/3.99  res_forward_subsumed:                   0
% 27.57/3.99  res_backward_subsumed:                  0
% 27.57/3.99  res_forward_subsumption_resolution:     0
% 27.57/3.99  res_backward_subsumption_resolution:    0
% 27.57/3.99  res_clause_to_clause_subsumption:       85352
% 27.57/3.99  res_orphan_elimination:                 0
% 27.57/3.99  res_tautology_del:                      824
% 27.57/3.99  res_num_eq_res_simplified:              0
% 27.57/3.99  res_num_sel_changes:                    0
% 27.57/3.99  res_moves_from_active_to_pass:          0
% 27.57/3.99  
% 27.57/3.99  ------ Superposition
% 27.57/3.99  
% 27.57/3.99  sup_time_total:                         0.
% 27.57/3.99  sup_time_generating:                    0.
% 27.57/3.99  sup_time_sim_full:                      0.
% 27.57/3.99  sup_time_sim_immed:                     0.
% 27.57/3.99  
% 27.57/3.99  sup_num_of_clauses:                     3438
% 27.57/3.99  sup_num_in_active:                      553
% 27.57/3.99  sup_num_in_passive:                     2885
% 27.57/3.99  sup_num_of_loops:                       630
% 27.57/3.99  sup_fw_superposition:                   5983
% 27.57/3.99  sup_bw_superposition:                   6109
% 27.57/3.99  sup_immediate_simplified:               7837
% 27.57/3.99  sup_given_eliminated:                   1
% 27.57/3.99  comparisons_done:                       0
% 27.57/3.99  comparisons_avoided:                    9
% 27.57/3.99  
% 27.57/3.99  ------ Simplifications
% 27.57/3.99  
% 27.57/3.99  
% 27.57/3.99  sim_fw_subset_subsumed:                 3077
% 27.57/3.99  sim_bw_subset_subsumed:                 712
% 27.57/3.99  sim_fw_subsumed:                        4072
% 27.57/3.99  sim_bw_subsumed:                        80
% 27.57/3.99  sim_fw_subsumption_res:                 0
% 27.57/3.99  sim_bw_subsumption_res:                 0
% 27.57/3.99  sim_tautology_del:                      67
% 27.57/3.99  sim_eq_tautology_del:                   50
% 27.57/3.99  sim_eq_res_simp:                        10
% 27.57/3.99  sim_fw_demodulated:                     1
% 27.57/3.99  sim_bw_demodulated:                     0
% 27.57/3.99  sim_light_normalised:                   0
% 27.57/3.99  sim_joinable_taut:                      0
% 27.57/3.99  sim_joinable_simp:                      0
% 27.57/3.99  sim_ac_normalised:                      0
% 27.57/3.99  sim_smt_subsumption:                    0
% 27.57/3.99  
%------------------------------------------------------------------------------
