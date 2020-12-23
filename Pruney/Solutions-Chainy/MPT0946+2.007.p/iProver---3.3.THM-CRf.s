%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:42 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  236 (10969 expanded)
%              Number of clauses        :  164 (3848 expanded)
%              Number of leaves         :   22 (2422 expanded)
%              Depth                    :   45
%              Number of atoms          :  900 (45794 expanded)
%              Number of equality atoms :  495 (15284 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK4 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4))
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK3 != X1
          & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( sK3 != sK4
    & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f48,f47])).

fof(f75,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f42])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & r2_hidden(sK2(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f49])).

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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f82,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_23,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_729,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_725,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_726,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_751,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_749,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2452,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_749])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_728,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3972,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_728])).

cnf(c_4393,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3972,c_749])).

cnf(c_4400,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4393,c_728])).

cnf(c_4492,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
    | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_4400])).

cnf(c_4515,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(superposition,[status(thm)],[c_725,c_4492])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_748,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_740,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4622,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_740])).

cnf(c_20,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_21,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_204,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_4627,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4622,c_204])).

cnf(c_2404,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2405,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2404])).

cnf(c_4776,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4627,c_2405])).

cnf(c_4777,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4776])).

cnf(c_4785,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | sK3 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_4777])).

cnf(c_29,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4841,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | sK3 = X0
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4785,c_29])).

cnf(c_4842,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | sK3 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4841])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_730,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4850,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_730])).

cnf(c_9481,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_29])).

cnf(c_9482,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9481])).

cnf(c_9490,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9482,c_730])).

cnf(c_4856,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_730])).

cnf(c_30,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10517,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4856,c_30])).

cnf(c_10518,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10517])).

cnf(c_10526,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10518,c_730])).

cnf(c_10913,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9490,c_29,c_30,c_4850,c_9776])).

cnf(c_10914,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10913])).

cnf(c_10922,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_726,c_10914])).

cnf(c_25,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_295,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_267,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_1041,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2620,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_730])).

cnf(c_5595,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2620,c_730])).

cnf(c_6041,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_5595])).

cnf(c_6069,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_725,c_6041])).

cnf(c_6291,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6069,c_25,c_295,c_1041])).

cnf(c_6292,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_6291])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_743,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6297,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6292,c_743])).

cnf(c_6586,plain,
    ( r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6297,c_2405])).

cnf(c_6587,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6586])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_731,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_893,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_732,c_731])).

cnf(c_6595,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6587,c_893])).

cnf(c_42,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1056,plain,
    ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1058,plain,
    ( ~ r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3))
    | ~ v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2208,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2210,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_3749,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_25])).

cnf(c_4412,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3749,c_28,c_27])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5876,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X3,k1_wellord1(k1_wellord2(X2),X1))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_270,c_22])).

cnf(c_5878,plain,
    ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3))
    | ~ r2_hidden(sK3,sK3)
    | ~ v3_ordinal1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5876])).

cnf(c_13,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_738,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6296,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6292,c_738])).

cnf(c_6311,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6296,c_204])).

cnf(c_2209,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2211,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_4414,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4412])).

cnf(c_6885,plain,
    ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6311,c_29,c_30,c_2211,c_2405,c_4414])).

cnf(c_6886,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6885])).

cnf(c_6892,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_6886])).

cnf(c_26,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_727,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_739,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1876,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_739])).

cnf(c_41,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_43,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_1979,plain,
    ( v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_43])).

cnf(c_1980,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1979])).

cnf(c_1985,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1980,c_731])).

cnf(c_6895,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6892,c_1985])).

cnf(c_6896,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6895])).

cnf(c_6902,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_6896])).

cnf(c_7027,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6902,c_30])).

cnf(c_7028,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_7027])).

cnf(c_7032,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7028,c_740])).

cnf(c_7037,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7032,c_204])).

cnf(c_7047,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3)
    | ~ v1_relat_1(k1_wellord2(sK3))
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7037])).

cnf(c_7049,plain,
    ( ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK3,sK3)
    | ~ v1_relat_1(k1_wellord2(sK3))
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_7047])).

cnf(c_7051,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6595,c_28,c_27,c_42,c_295,c_1058,c_2210,c_4412,c_5878,c_7049])).

cnf(c_742,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7054,plain,
    ( r2_hidden(sK4,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7051,c_742])).

cnf(c_1520,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_2152,plain,
    ( ~ r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2157,plain,
    ( r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_2159,plain,
    ( r2_hidden(sK4,k1_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_1220,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(k1_wellord2(X3),X2))
    | X2 != X0
    | k1_wellord1(k1_wellord2(X3),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_2143,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
    | ~ r2_hidden(sK4,X2)
    | X0 != sK4
    | k1_wellord1(k1_wellord2(X1),X0) != X2 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_2989,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,k1_wellord1(k1_wellord2(X1),sK4))
    | k1_wellord1(k1_wellord2(X1),sK4) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_5491,plain,
    ( r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4))
    | ~ r2_hidden(sK4,sK4)
    | k1_wellord1(k1_wellord2(X0),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2989])).

cnf(c_5492,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) != sK4
    | sK4 != sK4
    | r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4)) = iProver_top
    | r2_hidden(sK4,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5491])).

cnf(c_5494,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) != sK4
    | sK4 != sK4
    | r2_hidden(sK4,k1_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
    | r2_hidden(sK4,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5492])).

cnf(c_7428,plain,
    ( r2_hidden(sK4,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7054,c_28,c_27,c_42,c_43,c_295,c_1058,c_1520,c_2159,c_2210,c_4412,c_5494,c_5878,c_7049])).

cnf(c_9494,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | sK4 = sK3
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9482,c_7428])).

cnf(c_10932,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10922,c_30,c_25,c_295,c_1041,c_9494])).

cnf(c_10933,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_10932])).

cnf(c_7055,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7051,c_738])).

cnf(c_7067,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7055,c_204])).

cnf(c_35,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_37,plain,
    ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_7790,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7067,c_29,c_37,c_43])).

cnf(c_10938,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10933,c_7790])).

cnf(c_31,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_278,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_291,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_7437,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | sK4 = sK3
    | r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_7428])).

cnf(c_9766,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(sK4),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_9776,plain,
    ( k1_wellord1(k1_wellord2(sK4),X0) = X0
    | r2_hidden(X0,sK4) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9766])).

cnf(c_9778,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | r2_hidden(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9776])).

cnf(c_276,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1094,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X1 != k1_wellord2(sK4)
    | X0 != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_1198,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X0 != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_11171,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_11173,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11171])).

cnf(c_11175,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11173])).

cnf(c_11197,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10938,c_29,c_30,c_31,c_25,c_291,c_295,c_1041,c_4414,c_7437,c_7790,c_9778,c_11175])).

cnf(c_11203,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11197,c_738])).

cnf(c_11216,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11203,c_204])).

cnf(c_12067,plain,
    ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11216,c_30,c_31,c_25,c_291,c_295,c_1041,c_2405,c_4414,c_7437,c_7790,c_11175])).

cnf(c_12068,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12067])).

cnf(c_12073,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_12068])).

cnf(c_12551,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12073,c_1985])).

cnf(c_12557,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_12551])).

cnf(c_12560,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12557,c_30])).

cnf(c_12566,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12560,c_740])).

cnf(c_12602,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12566,c_204])).

cnf(c_12611,plain,
    ( r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK3,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12602])).

cnf(c_5877,plain,
    ( X0 != X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X0,k1_wellord1(k1_wellord2(X3),X2)) = iProver_top
    | v3_ordinal1(X2) != iProver_top
    | v3_ordinal1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5876])).

cnf(c_5879,plain,
    ( sK3 != sK3
    | r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) = iProver_top
    | r2_hidden(sK3,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5877])).

cnf(c_1057,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_1059,plain,
    ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12611,c_12557,c_11175,c_7790,c_5879,c_4414,c_1059,c_295,c_291,c_43,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.80/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/1.00  
% 3.80/1.00  ------  iProver source info
% 3.80/1.00  
% 3.80/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.80/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/1.00  git: non_committed_changes: false
% 3.80/1.00  git: last_make_outside_of_git: false
% 3.80/1.00  
% 3.80/1.00  ------ 
% 3.80/1.00  ------ Parsing...
% 3.80/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/1.00  
% 3.80/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/1.00  ------ Proving...
% 3.80/1.00  ------ Problem Properties 
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  clauses                                 29
% 3.80/1.00  conjectures                             4
% 3.80/1.00  EPR                                     8
% 3.80/1.00  Horn                                    20
% 3.80/1.00  unary                                   6
% 3.80/1.00  binary                                  3
% 3.80/1.00  lits                                    91
% 3.80/1.00  lits eq                                 15
% 3.80/1.00  fd_pure                                 0
% 3.80/1.00  fd_pseudo                               0
% 3.80/1.00  fd_cond                                 0
% 3.80/1.00  fd_pseudo_cond                          4
% 3.80/1.00  AC symbols                              0
% 3.80/1.00  
% 3.80/1.00  ------ Input Options Time Limit: Unbounded
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  ------ 
% 3.80/1.00  Current options:
% 3.80/1.00  ------ 
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  ------ Proving...
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  % SZS status Theorem for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  fof(f11,axiom,(
% 3.80/1.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f32,plain,(
% 3.80/1.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f11])).
% 3.80/1.00  
% 3.80/1.00  fof(f73,plain,(
% 3.80/1.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f32])).
% 3.80/1.00  
% 3.80/1.00  fof(f13,conjecture,(
% 3.80/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f14,negated_conjecture,(
% 3.80/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.80/1.00    inference(negated_conjecture,[],[f13])).
% 3.80/1.00  
% 3.80/1.00  fof(f34,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f14])).
% 3.80/1.00  
% 3.80/1.00  fof(f35,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.80/1.00    inference(flattening,[],[f34])).
% 3.80/1.00  
% 3.80/1.00  fof(f48,plain,(
% 3.80/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4)) & v3_ordinal1(sK4))) )),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f47,plain,(
% 3.80/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK3 != X1 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f49,plain,(
% 3.80/1.00    (sK3 != sK4 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f48,f47])).
% 3.80/1.00  
% 3.80/1.00  fof(f75,plain,(
% 3.80/1.00    v3_ordinal1(sK3)),
% 3.80/1.00    inference(cnf_transformation,[],[f49])).
% 3.80/1.00  
% 3.80/1.00  fof(f76,plain,(
% 3.80/1.00    v3_ordinal1(sK4)),
% 3.80/1.00    inference(cnf_transformation,[],[f49])).
% 3.80/1.00  
% 3.80/1.00  fof(f1,axiom,(
% 3.80/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f15,plain,(
% 3.80/1.00    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f1])).
% 3.80/1.00  
% 3.80/1.00  fof(f16,plain,(
% 3.80/1.00    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(flattening,[],[f15])).
% 3.80/1.00  
% 3.80/1.00  fof(f50,plain,(
% 3.80/1.00    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f16])).
% 3.80/1.00  
% 3.80/1.00  fof(f2,axiom,(
% 3.80/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f17,plain,(
% 3.80/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.80/1.00    inference(ennf_transformation,[],[f2])).
% 3.80/1.00  
% 3.80/1.00  fof(f18,plain,(
% 3.80/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(flattening,[],[f17])).
% 3.80/1.00  
% 3.80/1.00  fof(f36,plain,(
% 3.80/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(nnf_transformation,[],[f18])).
% 3.80/1.00  
% 3.80/1.00  fof(f51,plain,(
% 3.80/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f36])).
% 3.80/1.00  
% 3.80/1.00  fof(f12,axiom,(
% 3.80/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f33,plain,(
% 3.80/1.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.80/1.00    inference(ennf_transformation,[],[f12])).
% 3.80/1.00  
% 3.80/1.00  fof(f74,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f33])).
% 3.80/1.00  
% 3.80/1.00  fof(f3,axiom,(
% 3.80/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f19,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f3])).
% 3.80/1.00  
% 3.80/1.00  fof(f20,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(flattening,[],[f19])).
% 3.80/1.00  
% 3.80/1.00  fof(f53,plain,(
% 3.80/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f20])).
% 3.80/1.00  
% 3.80/1.00  fof(f5,axiom,(
% 3.80/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f22,plain,(
% 3.80/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.80/1.00    inference(ennf_transformation,[],[f5])).
% 3.80/1.00  
% 3.80/1.00  fof(f23,plain,(
% 3.80/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 3.80/1.00    inference(flattening,[],[f22])).
% 3.80/1.00  
% 3.80/1.00  fof(f60,plain,(
% 3.80/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f23])).
% 3.80/1.00  
% 3.80/1.00  fof(f8,axiom,(
% 3.80/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f28,plain,(
% 3.80/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(ennf_transformation,[],[f8])).
% 3.80/1.00  
% 3.80/1.00  fof(f29,plain,(
% 3.80/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(flattening,[],[f28])).
% 3.80/1.00  
% 3.80/1.00  fof(f42,plain,(
% 3.80/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(nnf_transformation,[],[f29])).
% 3.80/1.00  
% 3.80/1.00  fof(f43,plain,(
% 3.80/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(flattening,[],[f42])).
% 3.80/1.00  
% 3.80/1.00  fof(f44,plain,(
% 3.80/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(rectify,[],[f43])).
% 3.80/1.00  
% 3.80/1.00  fof(f45,plain,(
% 3.80/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f46,plain,(
% 3.80/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f45])).
% 3.80/1.00  
% 3.80/1.00  fof(f64,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f46])).
% 3.80/1.00  
% 3.80/1.00  fof(f89,plain,(
% 3.80/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.80/1.00    inference(equality_resolution,[],[f64])).
% 3.80/1.00  
% 3.80/1.00  fof(f9,axiom,(
% 3.80/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f71,plain,(
% 3.80/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.80/1.00    inference(cnf_transformation,[],[f9])).
% 3.80/1.00  
% 3.80/1.00  fof(f10,axiom,(
% 3.80/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f30,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f10])).
% 3.80/1.00  
% 3.80/1.00  fof(f31,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.80/1.00    inference(flattening,[],[f30])).
% 3.80/1.00  
% 3.80/1.00  fof(f72,plain,(
% 3.80/1.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f31])).
% 3.80/1.00  
% 3.80/1.00  fof(f78,plain,(
% 3.80/1.00    sK3 != sK4),
% 3.80/1.00    inference(cnf_transformation,[],[f49])).
% 3.80/1.00  
% 3.80/1.00  fof(f4,axiom,(
% 3.80/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f21,plain,(
% 3.80/1.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f4])).
% 3.80/1.00  
% 3.80/1.00  fof(f37,plain,(
% 3.80/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(nnf_transformation,[],[f21])).
% 3.80/1.00  
% 3.80/1.00  fof(f38,plain,(
% 3.80/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(flattening,[],[f37])).
% 3.80/1.00  
% 3.80/1.00  fof(f39,plain,(
% 3.80/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(rectify,[],[f38])).
% 3.80/1.00  
% 3.80/1.00  fof(f40,plain,(
% 3.80/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.80/1.00    introduced(choice_axiom,[])).
% 3.80/1.00  
% 3.80/1.00  fof(f41,plain,(
% 3.80/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.80/1.00  
% 3.80/1.00  fof(f55,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f41])).
% 3.80/1.00  
% 3.80/1.00  fof(f80,plain,(
% 3.80/1.00    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(equality_resolution,[],[f55])).
% 3.80/1.00  
% 3.80/1.00  fof(f65,plain,(
% 3.80/1.00    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f46])).
% 3.80/1.00  
% 3.80/1.00  fof(f88,plain,(
% 3.80/1.00    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.80/1.00    inference(equality_resolution,[],[f65])).
% 3.80/1.00  
% 3.80/1.00  fof(f54,plain,(
% 3.80/1.00    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f41])).
% 3.80/1.00  
% 3.80/1.00  fof(f81,plain,(
% 3.80/1.00    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(equality_resolution,[],[f54])).
% 3.80/1.00  
% 3.80/1.00  fof(f82,plain,(
% 3.80/1.00    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(equality_resolution,[],[f81])).
% 3.80/1.00  
% 3.80/1.00  fof(f7,axiom,(
% 3.80/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f26,plain,(
% 3.80/1.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f7])).
% 3.80/1.00  
% 3.80/1.00  fof(f27,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(flattening,[],[f26])).
% 3.80/1.00  
% 3.80/1.00  fof(f63,plain,(
% 3.80/1.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f27])).
% 3.80/1.00  
% 3.80/1.00  fof(f77,plain,(
% 3.80/1.00    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))),
% 3.80/1.00    inference(cnf_transformation,[],[f49])).
% 3.80/1.00  
% 3.80/1.00  fof(f6,axiom,(
% 3.80/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.80/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.80/1.00  
% 3.80/1.00  fof(f24,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(ennf_transformation,[],[f6])).
% 3.80/1.00  
% 3.80/1.00  fof(f25,plain,(
% 3.80/1.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.80/1.00    inference(flattening,[],[f24])).
% 3.80/1.00  
% 3.80/1.00  fof(f62,plain,(
% 3.80/1.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.80/1.00    inference(cnf_transformation,[],[f25])).
% 3.80/1.00  
% 3.80/1.00  cnf(c_23,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_729,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_28,negated_conjecture,
% 3.80/1.00      ( v3_ordinal1(sK3) ),
% 3.80/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_725,plain,
% 3.80/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_27,negated_conjecture,
% 3.80/1.00      ( v3_ordinal1(sK4) ),
% 3.80/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_726,plain,
% 3.80/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_0,plain,
% 3.80/1.00      ( r1_ordinal1(X0,X1)
% 3.80/1.00      | r1_ordinal1(X1,X0)
% 3.80/1.00      | ~ v3_ordinal1(X1)
% 3.80/1.00      | ~ v3_ordinal1(X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_751,plain,
% 3.80/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 3.80/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2,plain,
% 3.80/1.00      ( r1_tarski(X0,X1)
% 3.80/1.00      | ~ r1_ordinal1(X0,X1)
% 3.80/1.00      | ~ v3_ordinal1(X1)
% 3.80/1.00      | ~ v3_ordinal1(X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_749,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | r1_ordinal1(X0,X1) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2452,plain,
% 3.80/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_751,c_749]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_24,plain,
% 3.80/1.00      ( ~ r1_tarski(X0,X1)
% 3.80/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_728,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.80/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3972,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.80/1.00      | r1_ordinal1(X0,X1) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_2452,c_728]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4393,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.80/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_3972,c_749]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4400,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.80/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4393,c_728]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4492,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_726,c_4400]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4515,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_725,c_4492]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3,plain,
% 3.80/1.00      ( r2_hidden(X0,X1)
% 3.80/1.00      | r2_hidden(X1,X0)
% 3.80/1.00      | ~ v3_ordinal1(X1)
% 3.80/1.00      | ~ v3_ordinal1(X0)
% 3.80/1.00      | X0 = X1 ),
% 3.80/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_748,plain,
% 3.80/1.00      ( X0 = X1
% 3.80/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.80/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11,plain,
% 3.80/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 3.80/1.00      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
% 3.80/1.00      | ~ v1_relat_1(X1) ),
% 3.80/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_740,plain,
% 3.80/1.00      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
% 3.80/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4622,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4515,c_740]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_20,plain,
% 3.80/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.80/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.80/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_21,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_204,plain,
% 3.80/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_20,c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4627,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_4622,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2404,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(sK4)) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2405,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2404]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4776,plain,
% 3.80/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_4627,c_2405]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4777,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_4776]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4785,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_748,c_4777]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_29,plain,
% 3.80/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4841,plain,
% 3.80/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_4785,c_29]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4842,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_4841]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_22,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | ~ v3_ordinal1(X1)
% 3.80/1.00      | ~ v3_ordinal1(X0)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.80/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_730,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.80/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4850,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4842,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9481,plain,
% 3.80/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_4850,c_29]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9482,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(X0,sK4) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_9481]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9490,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_9482,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4856,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4842,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_30,plain,
% 3.80/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10517,plain,
% 3.80/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_4856,c_30]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10518,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_10517]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10526,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_10518,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10913,plain,
% 3.80/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_9490,c_29,c_30,c_4850,c_9776]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10914,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK3 = X0
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_10913]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10922,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),sK4) = sK4
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | sK4 = sK3 ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_726,c_10914]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_25,negated_conjecture,
% 3.80/1.00      ( sK3 != sK4 ),
% 3.80/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_295,plain,
% 3.80/1.00      ( sK3 = sK3 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_266]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_267,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1040,plain,
% 3.80/1.00      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_267]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1041,plain,
% 3.80/1.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1040]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2620,plain,
% 3.80/1.00      ( X0 = X1
% 3.80/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.80/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_748,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5595,plain,
% 3.80/1.00      ( X0 = X1
% 3.80/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.80/1.00      | v3_ordinal1(X1) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_2620,c_730]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6041,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | sK4 = X0
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_726,c_5595]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6069,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | sK4 = sK3 ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_725,c_6041]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6291,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6069,c_25,c_295,c_1041]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6292,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_6291]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_8,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 3.80/1.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 3.80/1.00      | ~ v1_relat_1(X1) ),
% 3.80/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_743,plain,
% 3.80/1.00      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 3.80/1.00      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 3.80/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6297,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_6292,c_743]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6586,plain,
% 3.80/1.00      ( r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6297,c_2405]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6587,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_6586]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_19,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X2,X1)
% 3.80/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 3.80/1.00      | r1_tarski(X2,X0)
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_732,plain,
% 3.80/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.80/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.80/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
% 3.80/1.00      | r1_tarski(X2,X0) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_731,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_893,plain,
% 3.80/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.80/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.80/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
% 3.80/1.00      | r1_tarski(X2,X0) = iProver_top ),
% 3.80/1.00      inference(forward_subsumption_resolution,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_732,c_731]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6595,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK4) != iProver_top
% 3.80/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_6587,c_893]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_42,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(sK3)) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 3.80/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1056,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1058,plain,
% 3.80/1.00      ( ~ r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3))
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(sK3)) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2208,plain,
% 3.80/1.00      ( ~ r2_hidden(sK4,X0)
% 3.80/1.00      | ~ v3_ordinal1(X0)
% 3.80/1.00      | ~ v3_ordinal1(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2210,plain,
% 3.80/1.00      ( ~ r2_hidden(sK4,sK3)
% 3.80/1.00      | ~ v3_ordinal1(sK4)
% 3.80/1.00      | ~ v3_ordinal1(sK3)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_2208]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_3749,plain,
% 3.80/1.00      ( r2_hidden(sK4,sK3)
% 3.80/1.00      | r2_hidden(sK3,sK4)
% 3.80/1.00      | ~ v3_ordinal1(sK4)
% 3.80/1.00      | ~ v3_ordinal1(sK3) ),
% 3.80/1.00      inference(resolution,[status(thm)],[c_3,c_25]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4412,plain,
% 3.80/1.00      ( r2_hidden(sK4,sK3) | r2_hidden(sK3,sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_3749,c_28,c_27]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_270,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.80/1.00      theory(equality) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5876,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | ~ r2_hidden(X1,X2)
% 3.80/1.00      | r2_hidden(X3,k1_wellord1(k1_wellord2(X2),X1))
% 3.80/1.00      | ~ v3_ordinal1(X1)
% 3.80/1.00      | ~ v3_ordinal1(X2)
% 3.80/1.00      | X3 != X0 ),
% 3.80/1.00      inference(resolution,[status(thm)],[c_270,c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5878,plain,
% 3.80/1.00      ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3))
% 3.80/1.00      | ~ r2_hidden(sK3,sK3)
% 3.80/1.00      | ~ v3_ordinal1(sK3)
% 3.80/1.00      | sK3 != sK3 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_5876]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_13,plain,
% 3.80/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.80/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.80/1.00      | ~ v2_wellord1(X0)
% 3.80/1.00      | ~ v1_relat_1(X0) ),
% 3.80/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_738,plain,
% 3.80/1.00      ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
% 3.80/1.00      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 3.80/1.00      | v2_wellord1(X0) != iProver_top
% 3.80/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6296,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_6292,c_738]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6311,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK4) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_6296,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2209,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 3.80/1.00      | r2_hidden(sK4,X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2211,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(sK4,sK3) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_4414,plain,
% 3.80/1.00      ( r2_hidden(sK4,sK3) = iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_4412]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6885,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6311,c_29,c_30,c_2211,c_2405,c_4414]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6886,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_6885]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6892,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4515,c_6886]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_26,negated_conjecture,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
% 3.80/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_727,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12,plain,
% 3.80/1.00      ( ~ r4_wellord1(X0,X1)
% 3.80/1.00      | r4_wellord1(X1,X0)
% 3.80/1.00      | ~ v1_relat_1(X0)
% 3.80/1.00      | ~ v1_relat_1(X1) ),
% 3.80/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_739,plain,
% 3.80/1.00      ( r4_wellord1(X0,X1) != iProver_top
% 3.80/1.00      | r4_wellord1(X1,X0) = iProver_top
% 3.80/1.00      | v1_relat_1(X0) != iProver_top
% 3.80/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1876,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_727,c_739]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_41,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_43,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_41]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1979,plain,
% 3.80/1.00      ( v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_1876,c_43]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1980,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_1979]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1985,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
% 3.80/1.00      inference(forward_subsumption_resolution,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_1980,c_731]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6895,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6892,c_1985]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6896,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_6895]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_6902,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_729,c_6896]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7027,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6902,c_30]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7028,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_7027]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7032,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_7028,c_740]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7037,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_7032,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7047,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,sK4)
% 3.80/1.00      | r2_hidden(X0,sK3)
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7037]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7049,plain,
% 3.80/1.00      ( ~ r2_hidden(sK3,sK4)
% 3.80/1.00      | r2_hidden(sK3,sK3)
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_7047]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7051,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_6595,c_28,c_27,c_42,c_295,c_1058,c_2210,c_4412,c_5878,
% 3.80/1.00                 c_7049]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_742,plain,
% 3.80/1.00      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 3.80/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7054,plain,
% 3.80/1.00      ( r2_hidden(sK4,sK4) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_7051,c_742]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1520,plain,
% 3.80/1.00      ( sK4 = sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_266]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2152,plain,
% 3.80/1.00      ( ~ r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4))
% 3.80/1.00      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2157,plain,
% 3.80/1.00      ( r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_2152]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2159,plain,
% 3.80/1.00      ( r2_hidden(sK4,k1_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_2157]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1220,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,X1)
% 3.80/1.00      | r2_hidden(X2,k1_wellord1(k1_wellord2(X3),X2))
% 3.80/1.00      | X2 != X0
% 3.80/1.00      | k1_wellord1(k1_wellord2(X3),X2) != X1 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_270]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2143,plain,
% 3.80/1.00      ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
% 3.80/1.00      | ~ r2_hidden(sK4,X2)
% 3.80/1.00      | X0 != sK4
% 3.80/1.00      | k1_wellord1(k1_wellord2(X1),X0) != X2 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1220]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_2989,plain,
% 3.80/1.00      ( ~ r2_hidden(sK4,X0)
% 3.80/1.00      | r2_hidden(sK4,k1_wellord1(k1_wellord2(X1),sK4))
% 3.80/1.00      | k1_wellord1(k1_wellord2(X1),sK4) != X0
% 3.80/1.00      | sK4 != sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_2143]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5491,plain,
% 3.80/1.00      ( r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4))
% 3.80/1.00      | ~ r2_hidden(sK4,sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(X0),sK4) != sK4
% 3.80/1.00      | sK4 != sK4 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_2989]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5492,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(X0),sK4) != sK4
% 3.80/1.00      | sK4 != sK4
% 3.80/1.00      | r2_hidden(sK4,k1_wellord1(k1_wellord2(X0),sK4)) = iProver_top
% 3.80/1.00      | r2_hidden(sK4,sK4) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_5491]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5494,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK3),sK4) != sK4
% 3.80/1.00      | sK4 != sK4
% 3.80/1.00      | r2_hidden(sK4,k1_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
% 3.80/1.00      | r2_hidden(sK4,sK4) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_5492]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7428,plain,
% 3.80/1.00      ( r2_hidden(sK4,sK4) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_7054,c_28,c_27,c_42,c_43,c_295,c_1058,c_1520,c_2159,
% 3.80/1.00                 c_2210,c_4412,c_5494,c_5878,c_7049]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9494,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | sK4 = sK3
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_9482,c_7428]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10932,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_10922,c_30,c_25,c_295,c_1041,c_9494]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10933,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_10932]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7055,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 3.80/1.00      | r2_hidden(sK4,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_7051,c_738]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7067,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 3.80/1.00      | r2_hidden(sK4,sK3) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_7055,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_35,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_37,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7790,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 3.80/1.00      | r2_hidden(sK4,sK3) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_7067,c_29,c_37,c_43]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_10938,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | r2_hidden(sK4,sK3) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_10933,c_7790]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_31,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_278,plain,
% 3.80/1.00      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 3.80/1.00      theory(equality) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_291,plain,
% 3.80/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK3) | sK3 != sK3 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_278]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_7437,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | sK4 = sK3
% 3.80/1.00      | r2_hidden(sK3,sK4) = iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4842,c_7428]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9766,plain,
% 3.80/1.00      ( ~ r2_hidden(X0,sK4)
% 3.80/1.00      | ~ v3_ordinal1(X0)
% 3.80/1.00      | ~ v3_ordinal1(sK4)
% 3.80/1.00      | k1_wellord1(k1_wellord2(sK4),X0) = X0 ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9776,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.80/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | v3_ordinal1(X0) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_9766]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_9778,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.80/1.00      | r2_hidden(sK3,sK4) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_9776]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_276,plain,
% 3.80/1.00      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.80/1.00      theory(equality) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1094,plain,
% 3.80/1.00      ( r4_wellord1(X0,X1)
% 3.80/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.80/1.00      | X1 != k1_wellord2(sK4)
% 3.80/1.00      | X0 != k1_wellord2(sK3) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_276]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1198,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),X0)
% 3.80/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.80/1.00      | X0 != k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1094]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11171,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
% 3.80/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.80/1.00      | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1198]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11173,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_11171]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11175,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
% 3.80/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_11173]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11197,plain,
% 3.80/1.00      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_10938,c_29,c_30,c_31,c_25,c_291,c_295,c_1041,c_4414,
% 3.80/1.00                 c_7437,c_7790,c_9778,c_11175]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11203,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_11197,c_738]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_11216,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK4) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_11203,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12067,plain,
% 3.80/1.00      ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_11216,c_30,c_31,c_25,c_291,c_295,c_1041,c_2405,c_4414,
% 3.80/1.00                 c_7437,c_7790,c_11175]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12068,plain,
% 3.80/1.00      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(renaming,[status(thm)],[c_12067]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12073,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_4515,c_12068]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12551,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_12073,c_1985]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12557,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.80/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_729,c_12551]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12560,plain,
% 3.80/1.00      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 3.80/1.00      inference(global_propositional_subsumption,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_12557,c_30]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12566,plain,
% 3.80/1.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 3.80/1.00      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(superposition,[status(thm)],[c_12560,c_740]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12602,plain,
% 3.80/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.80/1.00      | r2_hidden(X0,sK3) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(demodulation,[status(thm)],[c_12566,c_204]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_12611,plain,
% 3.80/1.00      ( r2_hidden(sK3,sK4) != iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK3) = iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_12602]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5877,plain,
% 3.80/1.00      ( X0 != X1
% 3.80/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.80/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.80/1.00      | r2_hidden(X0,k1_wellord1(k1_wellord2(X3),X2)) = iProver_top
% 3.80/1.00      | v3_ordinal1(X2) != iProver_top
% 3.80/1.00      | v3_ordinal1(X3) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_5876]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_5879,plain,
% 3.80/1.00      ( sK3 != sK3
% 3.80/1.00      | r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) = iProver_top
% 3.80/1.00      | r2_hidden(sK3,sK3) != iProver_top
% 3.80/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_5877]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1057,plain,
% 3.80/1.00      ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 3.80/1.00      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(c_1059,plain,
% 3.80/1.00      ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
% 3.80/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.80/1.00      inference(instantiation,[status(thm)],[c_1057]) ).
% 3.80/1.00  
% 3.80/1.00  cnf(contradiction,plain,
% 3.80/1.00      ( $false ),
% 3.80/1.00      inference(minisat,
% 3.80/1.00                [status(thm)],
% 3.80/1.00                [c_12611,c_12557,c_11175,c_7790,c_5879,c_4414,c_1059,
% 3.80/1.00                 c_295,c_291,c_43,c_31,c_30,c_29]) ).
% 3.80/1.00  
% 3.80/1.00  
% 3.80/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/1.00  
% 3.80/1.00  ------                               Statistics
% 3.80/1.00  
% 3.80/1.00  ------ Selected
% 3.80/1.00  
% 3.80/1.00  total_time:                             0.374
% 3.80/1.00  
%------------------------------------------------------------------------------
