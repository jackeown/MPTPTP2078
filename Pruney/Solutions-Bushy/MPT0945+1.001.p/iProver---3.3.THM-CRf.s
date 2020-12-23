%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0945+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 356 expanded)
%              Number of clauses        :  113 ( 136 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  768 (1558 expanded)
%              Number of equality atoms :  244 ( 417 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f57])).

fof(f82,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f64,f65])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f120,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).

fof(f88,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
             => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) != X0
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
     => ( k1_wellord1(k1_wellord2(sK6),X0) != X0
        & r2_hidden(X0,sK6)
        & v3_ordinal1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_wellord1(k1_wellord2(X1),X0) != X0
            & r2_hidden(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( k1_wellord1(k1_wellord2(X1),sK5) != sK5
          & r2_hidden(sK5,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( k1_wellord1(k1_wellord2(sK6),sK5) != sK5
    & r2_hidden(sK5,sK6)
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f70,f69])).

fof(f110,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f122,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f81])).

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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
      | sK0(X0,X1,X2) = X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    k1_wellord1(k1_wellord2(sK6),sK5) != sK5 ),
    inference(cnf_transformation,[],[f71])).

fof(f108,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3149,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5448,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X2)
    | X1 != X2
    | X0 != sK0(k1_wellord2(sK6),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_8751,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X1)
    | X1 != X0
    | sK0(k1_wellord2(sK6),sK5,sK5) != sK0(k1_wellord2(sK6),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5448])).

cnf(c_20928,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | sK0(k1_wellord2(sK6),sK5,sK5) != sK0(k1_wellord2(sK6),sK5,sK5)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_8751])).

cnf(c_30431,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),k3_relat_1(k1_wellord2(sK6)))
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | sK0(k1_wellord2(sK6),sK5,sK5) != sK0(k1_wellord2(sK6),sK5,sK5)
    | sK6 != k3_relat_1(k1_wellord2(sK6)) ),
    inference(instantiation,[status(thm)],[c_20928])).

cnf(c_30432,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != sK0(k1_wellord2(sK6),sK5,sK5)
    | sK6 != k3_relat_1(k1_wellord2(sK6))
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),k3_relat_1(k1_wellord2(sK6))) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30431])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_23,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_857,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | k1_wellord2(X3) != k1_wellord2(X2) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_4665,plain,
    ( r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6))
    | ~ r2_hidden(sK5,sK6)
    | k1_wellord2(X0) != k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_27352,plain,
    ( r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6))
    | ~ r2_hidden(sK5,sK6)
    | k1_wellord2(sK6) != k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_4665])).

cnf(c_27353,plain,
    ( k1_wellord2(sK6) != k1_wellord2(sK6)
    | r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27352])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5956,plain,
    ( ~ m1_subset_1(X0,sK6)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_27070,plain,
    ( ~ m1_subset_1(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | v3_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_5956])).

cnf(c_27071,plain,
    ( m1_subset_1(sK0(k1_wellord2(sK6),sK5,sK5),sK6) != iProver_top
    | v3_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27070])).

cnf(c_27,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5449,plain,
    ( m1_subset_1(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_12797,plain,
    ( m1_subset_1(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_5449])).

cnf(c_12804,plain,
    ( m1_subset_1(sK0(k1_wellord2(sK6),sK5,sK5),sK6) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12797])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5454,plain,
    ( ~ r2_hidden(X0,sK0(k1_wellord2(sK6),sK5,sK5))
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11864,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK0(k1_wellord2(sK6),sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_5454])).

cnf(c_11867,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK0(k1_wellord2(sK6),sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11864])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4477,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_11863,plain,
    ( ~ r1_tarski(sK5,sK0(k1_wellord2(sK6),sK5,sK5))
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK0(k1_wellord2(sK6),sK5,sK5))
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_4477])).

cnf(c_11865,plain,
    ( r1_tarski(sK5,sK0(k1_wellord2(sK6),sK5,sK5)) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK0(k1_wellord2(sK6),sK5,sK5)) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11863])).

cnf(c_11860,plain,
    ( ~ r1_tarski(sK5,sK6)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_4477])).

cnf(c_11861,plain,
    ( r1_tarski(sK5,sK6) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11860])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_875,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | k1_wellord2(X3) != k1_wellord2(X2) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_4982,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK6)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(sK6))
    | k1_wellord2(X2) != k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_6985,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK6)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(sK6))
    | k1_wellord2(sK6) != k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_4982])).

cnf(c_11743,plain,
    ( ~ r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6)
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6))
    | ~ r2_hidden(sK5,sK6)
    | k1_wellord2(sK6) != k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_6985])).

cnf(c_11744,plain,
    ( k1_wellord2(sK6) != k1_wellord2(sK6)
    | r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11743])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_9039,plain,
    ( r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | ~ v1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9040,plain,
    ( r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),X0) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9039])).

cnf(c_9042,plain,
    ( r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5) = iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top
    | v1_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9040])).

cnf(c_1,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8536,plain,
    ( ~ v3_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5))
    | v1_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8537,plain,
    ( v3_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) != iProver_top
    | v1_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8536])).

cnf(c_3148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5215,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_6654,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5215])).

cnf(c_8094,plain,
    ( k3_relat_1(k1_wellord2(sK6)) != sK6
    | sK6 = k3_relat_1(k1_wellord2(sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6654])).

cnf(c_3159,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7626,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,sK0(k1_wellord2(sK6),sK5,sK5))
    | sK0(k1_wellord2(sK6),sK5,sK5) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3159])).

cnf(c_7627,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != X0
    | sK5 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK5,sK0(k1_wellord2(sK6),sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7626])).

cnf(c_7629,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != sK5
    | sK5 != sK5
    | r1_tarski(sK5,sK0(k1_wellord2(sK6),sK5,sK5)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7627])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3983,plain,
    ( r2_hidden(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3992,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6031,plain,
    ( r1_tarski(sK5,sK6) = iProver_top
    | v1_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_3992])).

cnf(c_22,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_530,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_22,c_28])).

cnf(c_5494,plain,
    ( ~ r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0)
    | ~ v3_ordinal1(X0)
    | ~ v1_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5))
    | X0 = sK0(k1_wellord2(sK6),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_5495,plain,
    ( X0 = sK0(k1_wellord2(sK6),sK5,sK5)
    | r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),X0) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5494])).

cnf(c_5497,plain,
    ( sK5 = sK0(k1_wellord2(sK6),sK5,sK5)
    | r1_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(sK0(k1_wellord2(sK6),sK5,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5495])).

cnf(c_3147,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4791,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) = sK0(k1_wellord2(sK6),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_4459,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != X0
    | sK0(k1_wellord2(sK6),sK5,sK5) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_4790,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != sK0(k1_wellord2(sK6),sK5,sK5)
    | sK0(k1_wellord2(sK6),sK5,sK5) = sK5
    | sK5 != sK0(k1_wellord2(sK6),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_4459])).

cnf(c_31,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_699,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_23])).

cnf(c_700,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_4676,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),k3_relat_1(k1_wellord2(sK6)))
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_4677,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),k3_relat_1(k1_wellord2(sK6))) = iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4676])).

cnf(c_4585,plain,
    ( k1_wellord2(sK6) = k1_wellord2(sK6) ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_4516,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_15,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_245,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_23])).

cnf(c_4505,plain,
    ( k3_relat_1(k1_wellord2(sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
    | ~ v1_relat_1(X0)
    | sK0(X0,X1,X2) = X1
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_839,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
    | sK0(X0,X1,X2) = X1
    | k1_wellord1(X0,X1) = X2
    | k1_wellord2(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_840,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(X0),X1,X2),X2)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord2(X0),X1,X2),X1),k1_wellord2(X0))
    | sK0(k1_wellord2(X0),X1,X2) = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_4480,plain,
    ( ~ r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6))
    | sK0(k1_wellord2(sK6),sK5,sK5) = sK5
    | k1_wellord1(k1_wellord2(sK6),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_4481,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) = sK5
    | k1_wellord1(k1_wellord2(sK6),sK5) = sK5
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4480])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_824,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
    | k1_wellord1(X0,X1) = X2
    | k1_wellord2(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_825,plain,
    ( r2_hidden(sK0(k1_wellord2(X0),X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(k1_wellord2(X0),X1,X2),X1),k1_wellord2(X0))
    | k1_wellord1(k1_wellord2(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_4386,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6))
    | k1_wellord1(k1_wellord2(sK6),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_4387,plain,
    ( k1_wellord1(k1_wellord2(sK6),sK5) = sK5
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) = iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord2(sK6),sK5,sK5),sK5),k1_wellord2(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4386])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | sK0(X0,X1,X2) != X1
    | k1_wellord1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_809,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) != X1
    | k1_wellord1(X0,X1) = X2
    | k1_wellord2(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_810,plain,
    ( r2_hidden(sK0(k1_wellord2(X0),X1,X2),X2)
    | sK0(k1_wellord2(X0),X1,X2) != X1
    | k1_wellord1(k1_wellord2(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_4378,plain,
    ( r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5)
    | sK0(k1_wellord2(sK6),sK5,sK5) != sK5
    | k1_wellord1(k1_wellord2(sK6),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_4379,plain,
    ( sK0(k1_wellord2(sK6),sK5,sK5) != sK5
    | k1_wellord1(k1_wellord2(sK6),sK5) = sK5
    | r2_hidden(sK0(k1_wellord2(sK6),sK5,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4378])).

cnf(c_38,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4280,plain,
    ( v1_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_1,c_38])).

cnf(c_4281,plain,
    ( v1_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4280])).

cnf(c_141,plain,
    ( ~ r2_hidden(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_137,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_139,plain,
    ( v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_138,plain,
    ( ~ v3_ordinal1(sK5)
    | v1_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_81,plain,
    ( r2_xboole_0(sK5,sK5)
    | ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_71,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_73,plain,
    ( r1_ordinal1(sK5,sK5) != iProver_top
    | r1_tarski(sK5,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_72,plain,
    ( ~ r1_ordinal1(sK5,sK5)
    | r1_tarski(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_26,plain,
    ( r1_ordinal1(X0,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_68,plain,
    ( r1_ordinal1(X0,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_70,plain,
    ( r1_ordinal1(sK5,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_69,plain,
    ( r1_ordinal1(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_63,plain,
    ( ~ r2_xboole_0(sK5,sK5)
    | r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v1_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_36,negated_conjecture,
    ( k1_wellord1(k1_wellord2(sK6),sK5) != sK5 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_42,plain,
    ( r2_hidden(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_40,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30432,c_27353,c_27071,c_12804,c_11867,c_11865,c_11861,c_11744,c_9042,c_8537,c_8094,c_7629,c_6031,c_5497,c_4791,c_4790,c_4677,c_4585,c_4516,c_4505,c_4481,c_4387,c_4379,c_4281,c_141,c_139,c_138,c_81,c_73,c_72,c_70,c_69,c_63,c_36,c_42,c_41,c_40,c_39])).


%------------------------------------------------------------------------------
