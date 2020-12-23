%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:48 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 261 expanded)
%              Number of clauses        :   55 (  70 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  571 (1000 expanded)
%              Number of equality atoms :  229 ( 354 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f70,f89,f90,f89])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

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
     => ( ( ~ r1_tarski(sK8(X0,X1),sK9(X0,X1))
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( r1_tarski(sK8(X0,X1),sK9(X0,X1))
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK8(X0,X1),sK9(X0,X1))
              | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
            & ( r1_tarski(sK8(X0,X1),sK9(X0,X1))
              | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
            & r2_hidden(sK9(X0,X1),X0)
            & r2_hidden(sK8(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f43,f44])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f65,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f115,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f13,conjecture,(
    ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,
    ( ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0))
   => k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f21,f46])).

fof(f88,plain,(
    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(definition_unfolding,[],[f88,f90,f90])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f111,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f97])).

fof(f112,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f111])).

cnf(c_20,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1300,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3008,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
    | r1_tarski(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X3)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1300])).

cnf(c_25,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_440,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_441,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r1_tarski(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1293,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_28,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_479,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_480,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1290,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_35,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_200,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_36])).

cnf(c_1320,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1290,c_200])).

cnf(c_3837,plain,
    ( r2_hidden(sK6(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_1320])).

cnf(c_27,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_491,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_492,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_1319,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1289,c_200])).

cnf(c_3840,plain,
    ( r2_hidden(sK7(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_1319])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1304,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_452,plain,
    ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_453,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1)
    | r1_tarski(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1292,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_3110,plain,
    ( r2_hidden(sK7(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X2) != iProver_top
    | r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_1292])).

cnf(c_39134,plain,
    ( r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_3110])).

cnf(c_40331,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3837,c_39134])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1318,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_40521,plain,
    ( k2_zfmisc_1(X0,X0) = k1_wellord2(X0)
    | r1_tarski(k2_zfmisc_1(X0,X0),k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_40331,c_1318])).

cnf(c_40526,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k1_wellord2(k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3008,c_40521])).

cnf(c_40529,plain,
    ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
    | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40526])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
    | ~ r1_tarski(X0,X2)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_519,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
    | ~ r1_tarski(X0,X2)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_36,c_33])).

cnf(c_1464,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
    | ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
    | ~ r1_tarski(sK10,sK10)
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_1775,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
    | ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
    | ~ r1_tarski(sK10,sK10)
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_1776,plain,
    ( k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
    | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) = iProver_top
    | r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1756,plain,
    ( r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1406,plain,
    ( ~ r1_tarski(X0,k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
    | ~ r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),X0)
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1523,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_37,negated_conjecture,
    ( k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1496,plain,
    ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(demodulation,[status(thm)],[c_37,c_20])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_121,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_123,plain,
    ( r1_tarski(sK10,sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_108,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_110,plain,
    ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40529,c_1776,c_1756,c_1523,c_1496,c_123,c_110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.68/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.68/2.99  
% 19.68/2.99  ------  iProver source info
% 19.68/2.99  
% 19.68/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.68/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.68/2.99  git: non_committed_changes: false
% 19.68/2.99  git: last_make_outside_of_git: false
% 19.68/2.99  
% 19.68/2.99  ------ 
% 19.68/2.99  
% 19.68/2.99  ------ Input Options
% 19.68/2.99  
% 19.68/2.99  --out_options                           all
% 19.68/2.99  --tptp_safe_out                         true
% 19.68/2.99  --problem_path                          ""
% 19.68/2.99  --include_path                          ""
% 19.68/2.99  --clausifier                            res/vclausify_rel
% 19.68/2.99  --clausifier_options                    ""
% 19.68/2.99  --stdin                                 false
% 19.68/2.99  --stats_out                             all
% 19.68/2.99  
% 19.68/2.99  ------ General Options
% 19.68/2.99  
% 19.68/2.99  --fof                                   false
% 19.68/2.99  --time_out_real                         305.
% 19.68/2.99  --time_out_virtual                      -1.
% 19.68/2.99  --symbol_type_check                     false
% 19.68/2.99  --clausify_out                          false
% 19.68/2.99  --sig_cnt_out                           false
% 19.68/2.99  --trig_cnt_out                          false
% 19.68/2.99  --trig_cnt_out_tolerance                1.
% 19.68/2.99  --trig_cnt_out_sk_spl                   false
% 19.68/2.99  --abstr_cl_out                          false
% 19.68/2.99  
% 19.68/2.99  ------ Global Options
% 19.68/2.99  
% 19.68/2.99  --schedule                              default
% 19.68/2.99  --add_important_lit                     false
% 19.68/2.99  --prop_solver_per_cl                    1000
% 19.68/2.99  --min_unsat_core                        false
% 19.68/2.99  --soft_assumptions                      false
% 19.68/2.99  --soft_lemma_size                       3
% 19.68/2.99  --prop_impl_unit_size                   0
% 19.68/2.99  --prop_impl_unit                        []
% 19.68/2.99  --share_sel_clauses                     true
% 19.68/2.99  --reset_solvers                         false
% 19.68/2.99  --bc_imp_inh                            [conj_cone]
% 19.68/2.99  --conj_cone_tolerance                   3.
% 19.68/2.99  --extra_neg_conj                        none
% 19.68/2.99  --large_theory_mode                     true
% 19.68/2.99  --prolific_symb_bound                   200
% 19.68/2.99  --lt_threshold                          2000
% 19.68/2.99  --clause_weak_htbl                      true
% 19.68/2.99  --gc_record_bc_elim                     false
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing Options
% 19.68/2.99  
% 19.68/2.99  --preprocessing_flag                    true
% 19.68/2.99  --time_out_prep_mult                    0.1
% 19.68/2.99  --splitting_mode                        input
% 19.68/2.99  --splitting_grd                         true
% 19.68/2.99  --splitting_cvd                         false
% 19.68/2.99  --splitting_cvd_svl                     false
% 19.68/2.99  --splitting_nvd                         32
% 19.68/2.99  --sub_typing                            true
% 19.68/2.99  --prep_gs_sim                           true
% 19.68/2.99  --prep_unflatten                        true
% 19.68/2.99  --prep_res_sim                          true
% 19.68/2.99  --prep_upred                            true
% 19.68/2.99  --prep_sem_filter                       exhaustive
% 19.68/2.99  --prep_sem_filter_out                   false
% 19.68/2.99  --pred_elim                             true
% 19.68/2.99  --res_sim_input                         true
% 19.68/2.99  --eq_ax_congr_red                       true
% 19.68/2.99  --pure_diseq_elim                       true
% 19.68/2.99  --brand_transform                       false
% 19.68/2.99  --non_eq_to_eq                          false
% 19.68/2.99  --prep_def_merge                        true
% 19.68/2.99  --prep_def_merge_prop_impl              false
% 19.68/2.99  --prep_def_merge_mbd                    true
% 19.68/2.99  --prep_def_merge_tr_red                 false
% 19.68/2.99  --prep_def_merge_tr_cl                  false
% 19.68/2.99  --smt_preprocessing                     true
% 19.68/2.99  --smt_ac_axioms                         fast
% 19.68/2.99  --preprocessed_out                      false
% 19.68/2.99  --preprocessed_stats                    false
% 19.68/2.99  
% 19.68/2.99  ------ Abstraction refinement Options
% 19.68/2.99  
% 19.68/2.99  --abstr_ref                             []
% 19.68/2.99  --abstr_ref_prep                        false
% 19.68/2.99  --abstr_ref_until_sat                   false
% 19.68/2.99  --abstr_ref_sig_restrict                funpre
% 19.68/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/2.99  --abstr_ref_under                       []
% 19.68/2.99  
% 19.68/2.99  ------ SAT Options
% 19.68/2.99  
% 19.68/2.99  --sat_mode                              false
% 19.68/2.99  --sat_fm_restart_options                ""
% 19.68/2.99  --sat_gr_def                            false
% 19.68/2.99  --sat_epr_types                         true
% 19.68/2.99  --sat_non_cyclic_types                  false
% 19.68/2.99  --sat_finite_models                     false
% 19.68/2.99  --sat_fm_lemmas                         false
% 19.68/2.99  --sat_fm_prep                           false
% 19.68/2.99  --sat_fm_uc_incr                        true
% 19.68/2.99  --sat_out_model                         small
% 19.68/2.99  --sat_out_clauses                       false
% 19.68/2.99  
% 19.68/2.99  ------ QBF Options
% 19.68/2.99  
% 19.68/2.99  --qbf_mode                              false
% 19.68/2.99  --qbf_elim_univ                         false
% 19.68/2.99  --qbf_dom_inst                          none
% 19.68/2.99  --qbf_dom_pre_inst                      false
% 19.68/2.99  --qbf_sk_in                             false
% 19.68/2.99  --qbf_pred_elim                         true
% 19.68/2.99  --qbf_split                             512
% 19.68/2.99  
% 19.68/2.99  ------ BMC1 Options
% 19.68/2.99  
% 19.68/2.99  --bmc1_incremental                      false
% 19.68/2.99  --bmc1_axioms                           reachable_all
% 19.68/2.99  --bmc1_min_bound                        0
% 19.68/2.99  --bmc1_max_bound                        -1
% 19.68/2.99  --bmc1_max_bound_default                -1
% 19.68/2.99  --bmc1_symbol_reachability              true
% 19.68/2.99  --bmc1_property_lemmas                  false
% 19.68/2.99  --bmc1_k_induction                      false
% 19.68/2.99  --bmc1_non_equiv_states                 false
% 19.68/2.99  --bmc1_deadlock                         false
% 19.68/2.99  --bmc1_ucm                              false
% 19.68/2.99  --bmc1_add_unsat_core                   none
% 19.68/2.99  --bmc1_unsat_core_children              false
% 19.68/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/2.99  --bmc1_out_stat                         full
% 19.68/2.99  --bmc1_ground_init                      false
% 19.68/2.99  --bmc1_pre_inst_next_state              false
% 19.68/2.99  --bmc1_pre_inst_state                   false
% 19.68/2.99  --bmc1_pre_inst_reach_state             false
% 19.68/2.99  --bmc1_out_unsat_core                   false
% 19.68/2.99  --bmc1_aig_witness_out                  false
% 19.68/2.99  --bmc1_verbose                          false
% 19.68/2.99  --bmc1_dump_clauses_tptp                false
% 19.68/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.68/2.99  --bmc1_dump_file                        -
% 19.68/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.68/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.68/2.99  --bmc1_ucm_extend_mode                  1
% 19.68/2.99  --bmc1_ucm_init_mode                    2
% 19.68/2.99  --bmc1_ucm_cone_mode                    none
% 19.68/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.68/2.99  --bmc1_ucm_relax_model                  4
% 19.68/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.68/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/2.99  --bmc1_ucm_layered_model                none
% 19.68/2.99  --bmc1_ucm_max_lemma_size               10
% 19.68/2.99  
% 19.68/2.99  ------ AIG Options
% 19.68/2.99  
% 19.68/2.99  --aig_mode                              false
% 19.68/2.99  
% 19.68/2.99  ------ Instantiation Options
% 19.68/2.99  
% 19.68/2.99  --instantiation_flag                    true
% 19.68/2.99  --inst_sos_flag                         true
% 19.68/2.99  --inst_sos_phase                        true
% 19.68/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/2.99  --inst_lit_sel_side                     num_symb
% 19.68/2.99  --inst_solver_per_active                1400
% 19.68/2.99  --inst_solver_calls_frac                1.
% 19.68/2.99  --inst_passive_queue_type               priority_queues
% 19.68/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/2.99  --inst_passive_queues_freq              [25;2]
% 19.68/2.99  --inst_dismatching                      true
% 19.68/2.99  --inst_eager_unprocessed_to_passive     true
% 19.68/2.99  --inst_prop_sim_given                   true
% 19.68/2.99  --inst_prop_sim_new                     false
% 19.68/2.99  --inst_subs_new                         false
% 19.68/2.99  --inst_eq_res_simp                      false
% 19.68/2.99  --inst_subs_given                       false
% 19.68/2.99  --inst_orphan_elimination               true
% 19.68/2.99  --inst_learning_loop_flag               true
% 19.68/2.99  --inst_learning_start                   3000
% 19.68/2.99  --inst_learning_factor                  2
% 19.68/2.99  --inst_start_prop_sim_after_learn       3
% 19.68/2.99  --inst_sel_renew                        solver
% 19.68/2.99  --inst_lit_activity_flag                true
% 19.68/2.99  --inst_restr_to_given                   false
% 19.68/2.99  --inst_activity_threshold               500
% 19.68/2.99  --inst_out_proof                        true
% 19.68/2.99  
% 19.68/2.99  ------ Resolution Options
% 19.68/2.99  
% 19.68/2.99  --resolution_flag                       true
% 19.68/2.99  --res_lit_sel                           adaptive
% 19.68/2.99  --res_lit_sel_side                      none
% 19.68/2.99  --res_ordering                          kbo
% 19.68/2.99  --res_to_prop_solver                    active
% 19.68/2.99  --res_prop_simpl_new                    false
% 19.68/2.99  --res_prop_simpl_given                  true
% 19.68/2.99  --res_passive_queue_type                priority_queues
% 19.68/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/2.99  --res_passive_queues_freq               [15;5]
% 19.68/2.99  --res_forward_subs                      full
% 19.68/2.99  --res_backward_subs                     full
% 19.68/2.99  --res_forward_subs_resolution           true
% 19.68/2.99  --res_backward_subs_resolution          true
% 19.68/2.99  --res_orphan_elimination                true
% 19.68/2.99  --res_time_limit                        2.
% 19.68/2.99  --res_out_proof                         true
% 19.68/2.99  
% 19.68/2.99  ------ Superposition Options
% 19.68/2.99  
% 19.68/2.99  --superposition_flag                    true
% 19.68/2.99  --sup_passive_queue_type                priority_queues
% 19.68/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.68/2.99  --demod_completeness_check              fast
% 19.68/2.99  --demod_use_ground                      true
% 19.68/2.99  --sup_to_prop_solver                    passive
% 19.68/2.99  --sup_prop_simpl_new                    true
% 19.68/2.99  --sup_prop_simpl_given                  true
% 19.68/2.99  --sup_fun_splitting                     true
% 19.68/2.99  --sup_smt_interval                      50000
% 19.68/2.99  
% 19.68/2.99  ------ Superposition Simplification Setup
% 19.68/2.99  
% 19.68/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/2.99  --sup_immed_triv                        [TrivRules]
% 19.68/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_immed_bw_main                     []
% 19.68/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_input_bw                          []
% 19.68/2.99  
% 19.68/2.99  ------ Combination Options
% 19.68/2.99  
% 19.68/2.99  --comb_res_mult                         3
% 19.68/2.99  --comb_sup_mult                         2
% 19.68/2.99  --comb_inst_mult                        10
% 19.68/2.99  
% 19.68/2.99  ------ Debug Options
% 19.68/2.99  
% 19.68/2.99  --dbg_backtrace                         false
% 19.68/2.99  --dbg_dump_prop_clauses                 false
% 19.68/2.99  --dbg_dump_prop_clauses_file            -
% 19.68/2.99  --dbg_out_stat                          false
% 19.68/2.99  ------ Parsing...
% 19.68/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.68/2.99  ------ Proving...
% 19.68/2.99  ------ Problem Properties 
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  clauses                                 36
% 19.68/2.99  conjectures                             1
% 19.68/2.99  EPR                                     2
% 19.68/2.99  Horn                                    27
% 19.68/2.99  unary                                   8
% 19.68/2.99  binary                                  11
% 19.68/2.99  lits                                    90
% 19.68/2.99  lits eq                                 31
% 19.68/2.99  fd_pure                                 0
% 19.68/2.99  fd_pseudo                               0
% 19.68/2.99  fd_cond                                 0
% 19.68/2.99  fd_pseudo_cond                          9
% 19.68/2.99  AC symbols                              0
% 19.68/2.99  
% 19.68/2.99  ------ Schedule dynamic 5 is on 
% 19.68/2.99  
% 19.68/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  ------ 
% 19.68/2.99  Current options:
% 19.68/2.99  ------ 
% 19.68/2.99  
% 19.68/2.99  ------ Input Options
% 19.68/2.99  
% 19.68/2.99  --out_options                           all
% 19.68/2.99  --tptp_safe_out                         true
% 19.68/2.99  --problem_path                          ""
% 19.68/2.99  --include_path                          ""
% 19.68/2.99  --clausifier                            res/vclausify_rel
% 19.68/2.99  --clausifier_options                    ""
% 19.68/2.99  --stdin                                 false
% 19.68/2.99  --stats_out                             all
% 19.68/2.99  
% 19.68/2.99  ------ General Options
% 19.68/2.99  
% 19.68/2.99  --fof                                   false
% 19.68/2.99  --time_out_real                         305.
% 19.68/2.99  --time_out_virtual                      -1.
% 19.68/2.99  --symbol_type_check                     false
% 19.68/2.99  --clausify_out                          false
% 19.68/2.99  --sig_cnt_out                           false
% 19.68/2.99  --trig_cnt_out                          false
% 19.68/2.99  --trig_cnt_out_tolerance                1.
% 19.68/2.99  --trig_cnt_out_sk_spl                   false
% 19.68/2.99  --abstr_cl_out                          false
% 19.68/2.99  
% 19.68/2.99  ------ Global Options
% 19.68/2.99  
% 19.68/2.99  --schedule                              default
% 19.68/2.99  --add_important_lit                     false
% 19.68/2.99  --prop_solver_per_cl                    1000
% 19.68/2.99  --min_unsat_core                        false
% 19.68/2.99  --soft_assumptions                      false
% 19.68/2.99  --soft_lemma_size                       3
% 19.68/2.99  --prop_impl_unit_size                   0
% 19.68/2.99  --prop_impl_unit                        []
% 19.68/2.99  --share_sel_clauses                     true
% 19.68/2.99  --reset_solvers                         false
% 19.68/2.99  --bc_imp_inh                            [conj_cone]
% 19.68/2.99  --conj_cone_tolerance                   3.
% 19.68/2.99  --extra_neg_conj                        none
% 19.68/2.99  --large_theory_mode                     true
% 19.68/2.99  --prolific_symb_bound                   200
% 19.68/2.99  --lt_threshold                          2000
% 19.68/2.99  --clause_weak_htbl                      true
% 19.68/2.99  --gc_record_bc_elim                     false
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing Options
% 19.68/2.99  
% 19.68/2.99  --preprocessing_flag                    true
% 19.68/2.99  --time_out_prep_mult                    0.1
% 19.68/2.99  --splitting_mode                        input
% 19.68/2.99  --splitting_grd                         true
% 19.68/2.99  --splitting_cvd                         false
% 19.68/2.99  --splitting_cvd_svl                     false
% 19.68/2.99  --splitting_nvd                         32
% 19.68/2.99  --sub_typing                            true
% 19.68/2.99  --prep_gs_sim                           true
% 19.68/2.99  --prep_unflatten                        true
% 19.68/2.99  --prep_res_sim                          true
% 19.68/2.99  --prep_upred                            true
% 19.68/2.99  --prep_sem_filter                       exhaustive
% 19.68/2.99  --prep_sem_filter_out                   false
% 19.68/2.99  --pred_elim                             true
% 19.68/2.99  --res_sim_input                         true
% 19.68/2.99  --eq_ax_congr_red                       true
% 19.68/2.99  --pure_diseq_elim                       true
% 19.68/2.99  --brand_transform                       false
% 19.68/2.99  --non_eq_to_eq                          false
% 19.68/2.99  --prep_def_merge                        true
% 19.68/2.99  --prep_def_merge_prop_impl              false
% 19.68/2.99  --prep_def_merge_mbd                    true
% 19.68/2.99  --prep_def_merge_tr_red                 false
% 19.68/2.99  --prep_def_merge_tr_cl                  false
% 19.68/2.99  --smt_preprocessing                     true
% 19.68/2.99  --smt_ac_axioms                         fast
% 19.68/2.99  --preprocessed_out                      false
% 19.68/2.99  --preprocessed_stats                    false
% 19.68/2.99  
% 19.68/2.99  ------ Abstraction refinement Options
% 19.68/2.99  
% 19.68/2.99  --abstr_ref                             []
% 19.68/2.99  --abstr_ref_prep                        false
% 19.68/2.99  --abstr_ref_until_sat                   false
% 19.68/2.99  --abstr_ref_sig_restrict                funpre
% 19.68/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.68/2.99  --abstr_ref_under                       []
% 19.68/2.99  
% 19.68/2.99  ------ SAT Options
% 19.68/2.99  
% 19.68/2.99  --sat_mode                              false
% 19.68/2.99  --sat_fm_restart_options                ""
% 19.68/2.99  --sat_gr_def                            false
% 19.68/2.99  --sat_epr_types                         true
% 19.68/2.99  --sat_non_cyclic_types                  false
% 19.68/2.99  --sat_finite_models                     false
% 19.68/2.99  --sat_fm_lemmas                         false
% 19.68/2.99  --sat_fm_prep                           false
% 19.68/2.99  --sat_fm_uc_incr                        true
% 19.68/2.99  --sat_out_model                         small
% 19.68/2.99  --sat_out_clauses                       false
% 19.68/2.99  
% 19.68/2.99  ------ QBF Options
% 19.68/2.99  
% 19.68/2.99  --qbf_mode                              false
% 19.68/2.99  --qbf_elim_univ                         false
% 19.68/2.99  --qbf_dom_inst                          none
% 19.68/2.99  --qbf_dom_pre_inst                      false
% 19.68/2.99  --qbf_sk_in                             false
% 19.68/2.99  --qbf_pred_elim                         true
% 19.68/2.99  --qbf_split                             512
% 19.68/2.99  
% 19.68/2.99  ------ BMC1 Options
% 19.68/2.99  
% 19.68/2.99  --bmc1_incremental                      false
% 19.68/2.99  --bmc1_axioms                           reachable_all
% 19.68/2.99  --bmc1_min_bound                        0
% 19.68/2.99  --bmc1_max_bound                        -1
% 19.68/2.99  --bmc1_max_bound_default                -1
% 19.68/2.99  --bmc1_symbol_reachability              true
% 19.68/2.99  --bmc1_property_lemmas                  false
% 19.68/2.99  --bmc1_k_induction                      false
% 19.68/2.99  --bmc1_non_equiv_states                 false
% 19.68/2.99  --bmc1_deadlock                         false
% 19.68/2.99  --bmc1_ucm                              false
% 19.68/2.99  --bmc1_add_unsat_core                   none
% 19.68/2.99  --bmc1_unsat_core_children              false
% 19.68/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.68/2.99  --bmc1_out_stat                         full
% 19.68/2.99  --bmc1_ground_init                      false
% 19.68/2.99  --bmc1_pre_inst_next_state              false
% 19.68/2.99  --bmc1_pre_inst_state                   false
% 19.68/2.99  --bmc1_pre_inst_reach_state             false
% 19.68/2.99  --bmc1_out_unsat_core                   false
% 19.68/2.99  --bmc1_aig_witness_out                  false
% 19.68/2.99  --bmc1_verbose                          false
% 19.68/2.99  --bmc1_dump_clauses_tptp                false
% 19.68/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.68/2.99  --bmc1_dump_file                        -
% 19.68/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.68/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.68/2.99  --bmc1_ucm_extend_mode                  1
% 19.68/2.99  --bmc1_ucm_init_mode                    2
% 19.68/2.99  --bmc1_ucm_cone_mode                    none
% 19.68/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.68/2.99  --bmc1_ucm_relax_model                  4
% 19.68/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.68/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.68/2.99  --bmc1_ucm_layered_model                none
% 19.68/2.99  --bmc1_ucm_max_lemma_size               10
% 19.68/2.99  
% 19.68/2.99  ------ AIG Options
% 19.68/2.99  
% 19.68/2.99  --aig_mode                              false
% 19.68/2.99  
% 19.68/2.99  ------ Instantiation Options
% 19.68/2.99  
% 19.68/2.99  --instantiation_flag                    true
% 19.68/2.99  --inst_sos_flag                         true
% 19.68/2.99  --inst_sos_phase                        true
% 19.68/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.68/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.68/2.99  --inst_lit_sel_side                     none
% 19.68/2.99  --inst_solver_per_active                1400
% 19.68/2.99  --inst_solver_calls_frac                1.
% 19.68/2.99  --inst_passive_queue_type               priority_queues
% 19.68/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.68/2.99  --inst_passive_queues_freq              [25;2]
% 19.68/2.99  --inst_dismatching                      true
% 19.68/2.99  --inst_eager_unprocessed_to_passive     true
% 19.68/2.99  --inst_prop_sim_given                   true
% 19.68/2.99  --inst_prop_sim_new                     false
% 19.68/2.99  --inst_subs_new                         false
% 19.68/2.99  --inst_eq_res_simp                      false
% 19.68/2.99  --inst_subs_given                       false
% 19.68/2.99  --inst_orphan_elimination               true
% 19.68/2.99  --inst_learning_loop_flag               true
% 19.68/2.99  --inst_learning_start                   3000
% 19.68/2.99  --inst_learning_factor                  2
% 19.68/2.99  --inst_start_prop_sim_after_learn       3
% 19.68/2.99  --inst_sel_renew                        solver
% 19.68/2.99  --inst_lit_activity_flag                true
% 19.68/2.99  --inst_restr_to_given                   false
% 19.68/2.99  --inst_activity_threshold               500
% 19.68/2.99  --inst_out_proof                        true
% 19.68/2.99  
% 19.68/2.99  ------ Resolution Options
% 19.68/2.99  
% 19.68/2.99  --resolution_flag                       false
% 19.68/2.99  --res_lit_sel                           adaptive
% 19.68/2.99  --res_lit_sel_side                      none
% 19.68/2.99  --res_ordering                          kbo
% 19.68/2.99  --res_to_prop_solver                    active
% 19.68/2.99  --res_prop_simpl_new                    false
% 19.68/2.99  --res_prop_simpl_given                  true
% 19.68/2.99  --res_passive_queue_type                priority_queues
% 19.68/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.68/2.99  --res_passive_queues_freq               [15;5]
% 19.68/2.99  --res_forward_subs                      full
% 19.68/2.99  --res_backward_subs                     full
% 19.68/2.99  --res_forward_subs_resolution           true
% 19.68/2.99  --res_backward_subs_resolution          true
% 19.68/2.99  --res_orphan_elimination                true
% 19.68/2.99  --res_time_limit                        2.
% 19.68/2.99  --res_out_proof                         true
% 19.68/2.99  
% 19.68/2.99  ------ Superposition Options
% 19.68/2.99  
% 19.68/2.99  --superposition_flag                    true
% 19.68/2.99  --sup_passive_queue_type                priority_queues
% 19.68/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.68/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.68/2.99  --demod_completeness_check              fast
% 19.68/2.99  --demod_use_ground                      true
% 19.68/2.99  --sup_to_prop_solver                    passive
% 19.68/2.99  --sup_prop_simpl_new                    true
% 19.68/2.99  --sup_prop_simpl_given                  true
% 19.68/2.99  --sup_fun_splitting                     true
% 19.68/2.99  --sup_smt_interval                      50000
% 19.68/2.99  
% 19.68/2.99  ------ Superposition Simplification Setup
% 19.68/2.99  
% 19.68/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.68/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.68/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.68/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.68/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.68/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.68/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.68/2.99  --sup_immed_triv                        [TrivRules]
% 19.68/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_immed_bw_main                     []
% 19.68/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.68/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.68/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.68/2.99  --sup_input_bw                          []
% 19.68/2.99  
% 19.68/2.99  ------ Combination Options
% 19.68/2.99  
% 19.68/2.99  --comb_res_mult                         3
% 19.68/2.99  --comb_sup_mult                         2
% 19.68/2.99  --comb_inst_mult                        10
% 19.68/2.99  
% 19.68/2.99  ------ Debug Options
% 19.68/2.99  
% 19.68/2.99  --dbg_backtrace                         false
% 19.68/2.99  --dbg_dump_prop_clauses                 false
% 19.68/2.99  --dbg_dump_prop_clauses_file            -
% 19.68/2.99  --dbg_out_stat                          false
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  ------ Proving...
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  % SZS status Theorem for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  fof(f7,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f70,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 19.68/2.99    inference(cnf_transformation,[],[f7])).
% 19.68/2.99  
% 19.68/2.99  fof(f3,axiom,(
% 19.68/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f59,plain,(
% 19.68/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f3])).
% 19.68/2.99  
% 19.68/2.99  fof(f90,plain,(
% 19.68/2.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.68/2.99    inference(definition_unfolding,[],[f59,f89])).
% 19.68/2.99  
% 19.68/2.99  fof(f4,axiom,(
% 19.68/2.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f60,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f4])).
% 19.68/2.99  
% 19.68/2.99  fof(f5,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f61,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f5])).
% 19.68/2.99  
% 19.68/2.99  fof(f89,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.68/2.99    inference(definition_unfolding,[],[f60,f61])).
% 19.68/2.99  
% 19.68/2.99  fof(f100,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 19.68/2.99    inference(definition_unfolding,[],[f70,f89,f90,f89])).
% 19.68/2.99  
% 19.68/2.99  fof(f8,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f35,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.68/2.99    inference(nnf_transformation,[],[f8])).
% 19.68/2.99  
% 19.68/2.99  fof(f36,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 19.68/2.99    inference(flattening,[],[f35])).
% 19.68/2.99  
% 19.68/2.99  fof(f74,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f36])).
% 19.68/2.99  
% 19.68/2.99  fof(f101,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 19.68/2.99    inference(definition_unfolding,[],[f74,f89])).
% 19.68/2.99  
% 19.68/2.99  fof(f9,axiom,(
% 19.68/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f16,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 19.68/2.99    inference(ennf_transformation,[],[f9])).
% 19.68/2.99  
% 19.68/2.99  fof(f37,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 19.68/2.99    inference(nnf_transformation,[],[f16])).
% 19.68/2.99  
% 19.68/2.99  fof(f38,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 19.68/2.99    inference(rectify,[],[f37])).
% 19.68/2.99  
% 19.68/2.99  fof(f39,plain,(
% 19.68/2.99    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f40,plain,(
% 19.68/2.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).
% 19.68/2.99  
% 19.68/2.99  fof(f76,plain,(
% 19.68/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f12,axiom,(
% 19.68/2.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f87,plain,(
% 19.68/2.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 19.68/2.99    inference(cnf_transformation,[],[f12])).
% 19.68/2.99  
% 19.68/2.99  fof(f10,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f17,plain,(
% 19.68/2.99    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 19.68/2.99    inference(ennf_transformation,[],[f10])).
% 19.68/2.99  
% 19.68/2.99  fof(f18,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.68/2.99    inference(flattening,[],[f17])).
% 19.68/2.99  
% 19.68/2.99  fof(f78,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f18])).
% 19.68/2.99  
% 19.68/2.99  fof(f11,axiom,(
% 19.68/2.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f19,plain,(
% 19.68/2.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(ennf_transformation,[],[f11])).
% 19.68/2.99  
% 19.68/2.99  fof(f20,plain,(
% 19.68/2.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(flattening,[],[f19])).
% 19.68/2.99  
% 19.68/2.99  fof(f41,plain,(
% 19.68/2.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(nnf_transformation,[],[f20])).
% 19.68/2.99  
% 19.68/2.99  fof(f42,plain,(
% 19.68/2.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(flattening,[],[f41])).
% 19.68/2.99  
% 19.68/2.99  fof(f43,plain,(
% 19.68/2.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(rectify,[],[f42])).
% 19.68/2.99  
% 19.68/2.99  fof(f44,plain,(
% 19.68/2.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK8(X0,X1),sK9(X0,X1)) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r1_tarski(sK8(X0,X1),sK9(X0,X1)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0)))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f45,plain,(
% 19.68/2.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK8(X0,X1),sK9(X0,X1)) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r1_tarski(sK8(X0,X1),sK9(X0,X1)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f43,f44])).
% 19.68/2.99  
% 19.68/2.99  fof(f80,plain,(
% 19.68/2.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f45])).
% 19.68/2.99  
% 19.68/2.99  fof(f125,plain,(
% 19.68/2.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 19.68/2.99    inference(equality_resolution,[],[f80])).
% 19.68/2.99  
% 19.68/2.99  fof(f79,plain,(
% 19.68/2.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f18])).
% 19.68/2.99  
% 19.68/2.99  fof(f6,axiom,(
% 19.68/2.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f29,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.68/2.99    inference(nnf_transformation,[],[f6])).
% 19.68/2.99  
% 19.68/2.99  fof(f30,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.68/2.99    inference(rectify,[],[f29])).
% 19.68/2.99  
% 19.68/2.99  fof(f33,plain,(
% 19.68/2.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f32,plain,(
% 19.68/2.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f31,plain,(
% 19.68/2.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f34,plain,(
% 19.68/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 19.68/2.99  
% 19.68/2.99  fof(f65,plain,(
% 19.68/2.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.68/2.99    inference(cnf_transformation,[],[f34])).
% 19.68/2.99  
% 19.68/2.99  fof(f114,plain,(
% 19.68/2.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.68/2.99    inference(equality_resolution,[],[f65])).
% 19.68/2.99  
% 19.68/2.99  fof(f115,plain,(
% 19.68/2.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 19.68/2.99    inference(equality_resolution,[],[f114])).
% 19.68/2.99  
% 19.68/2.99  fof(f77,plain,(
% 19.68/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f40])).
% 19.68/2.99  
% 19.68/2.99  fof(f1,axiom,(
% 19.68/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f22,plain,(
% 19.68/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.68/2.99    inference(nnf_transformation,[],[f1])).
% 19.68/2.99  
% 19.68/2.99  fof(f23,plain,(
% 19.68/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.68/2.99    inference(flattening,[],[f22])).
% 19.68/2.99  
% 19.68/2.99  fof(f50,plain,(
% 19.68/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f23])).
% 19.68/2.99  
% 19.68/2.99  fof(f82,plain,(
% 19.68/2.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 19.68/2.99    inference(cnf_transformation,[],[f45])).
% 19.68/2.99  
% 19.68/2.99  fof(f123,plain,(
% 19.68/2.99    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 19.68/2.99    inference(equality_resolution,[],[f82])).
% 19.68/2.99  
% 19.68/2.99  fof(f49,plain,(
% 19.68/2.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.68/2.99    inference(cnf_transformation,[],[f23])).
% 19.68/2.99  
% 19.68/2.99  fof(f105,plain,(
% 19.68/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.68/2.99    inference(equality_resolution,[],[f49])).
% 19.68/2.99  
% 19.68/2.99  fof(f13,conjecture,(
% 19.68/2.99    ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f14,negated_conjecture,(
% 19.68/2.99    ~! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0))),
% 19.68/2.99    inference(negated_conjecture,[],[f13])).
% 19.68/2.99  
% 19.68/2.99  fof(f21,plain,(
% 19.68/2.99    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0))),
% 19.68/2.99    inference(ennf_transformation,[],[f14])).
% 19.68/2.99  
% 19.68/2.99  fof(f46,plain,(
% 19.68/2.99    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0)) => k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f47,plain,(
% 19.68/2.99    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f21,f46])).
% 19.68/2.99  
% 19.68/2.99  fof(f88,plain,(
% 19.68/2.99    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 19.68/2.99    inference(cnf_transformation,[],[f47])).
% 19.68/2.99  
% 19.68/2.99  fof(f104,plain,(
% 19.68/2.99    k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))),
% 19.68/2.99    inference(definition_unfolding,[],[f88,f90,f90])).
% 19.68/2.99  
% 19.68/2.99  fof(f48,plain,(
% 19.68/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.68/2.99    inference(cnf_transformation,[],[f23])).
% 19.68/2.99  
% 19.68/2.99  fof(f106,plain,(
% 19.68/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.68/2.99    inference(equality_resolution,[],[f48])).
% 19.68/2.99  
% 19.68/2.99  fof(f2,axiom,(
% 19.68/2.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 19.68/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/2.99  
% 19.68/2.99  fof(f15,plain,(
% 19.68/2.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 19.68/2.99    inference(ennf_transformation,[],[f2])).
% 19.68/2.99  
% 19.68/2.99  fof(f24,plain,(
% 19.68/2.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.68/2.99    inference(nnf_transformation,[],[f15])).
% 19.68/2.99  
% 19.68/2.99  fof(f25,plain,(
% 19.68/2.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.68/2.99    inference(flattening,[],[f24])).
% 19.68/2.99  
% 19.68/2.99  fof(f26,plain,(
% 19.68/2.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.68/2.99    inference(rectify,[],[f25])).
% 19.68/2.99  
% 19.68/2.99  fof(f27,plain,(
% 19.68/2.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 19.68/2.99    introduced(choice_axiom,[])).
% 19.68/2.99  
% 19.68/2.99  fof(f28,plain,(
% 19.68/2.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.68/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 19.68/2.99  
% 19.68/2.99  fof(f52,plain,(
% 19.68/2.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.68/2.99    inference(cnf_transformation,[],[f28])).
% 19.68/2.99  
% 19.68/2.99  fof(f97,plain,(
% 19.68/2.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 19.68/2.99    inference(definition_unfolding,[],[f52,f61])).
% 19.68/2.99  
% 19.68/2.99  fof(f111,plain,(
% 19.68/2.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 19.68/2.99    inference(equality_resolution,[],[f97])).
% 19.68/2.99  
% 19.68/2.99  fof(f112,plain,(
% 19.68/2.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 19.68/2.99    inference(equality_resolution,[],[f111])).
% 19.68/2.99  
% 19.68/2.99  cnf(c_20,plain,
% 19.68/2.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f100]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_21,plain,
% 19.68/2.99      ( ~ r2_hidden(X0,X1)
% 19.68/2.99      | ~ r2_hidden(X2,X1)
% 19.68/2.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f101]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1300,plain,
% 19.68/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.68/2.99      | r2_hidden(X2,X1) != iProver_top
% 19.68/2.99      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_3008,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X3),X2) != iProver_top
% 19.68/2.99      | r1_tarski(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X3)),X2) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_20,c_1300]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_25,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
% 19.68/2.99      | r1_tarski(X0,X1)
% 19.68/2.99      | ~ v1_relat_1(X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_36,plain,
% 19.68/2.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f87]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_440,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
% 19.68/2.99      | r1_tarski(X0,X1)
% 19.68/2.99      | k1_wellord2(X2) != X0 ),
% 19.68/2.99      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_441,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0))
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) ),
% 19.68/2.99      inference(unflattening,[status(thm)],[c_440]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1293,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_28,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(X1))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.68/2.99      | ~ v1_relat_1(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_479,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(X1))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.68/2.99      | k1_wellord2(X3) != X1 ),
% 19.68/2.99      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_480,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
% 19.68/2.99      inference(unflattening,[status(thm)],[c_479]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1290,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_35,plain,
% 19.68/2.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 19.68/2.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 19.68/2.99      inference(cnf_transformation,[],[f125]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_200,plain,
% 19.68/2.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 19.68/2.99      inference(global_propositional_subsumption,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_35,c_36]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1320,plain,
% 19.68/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_1290,c_200]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_3837,plain,
% 19.68/2.99      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0) = iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_1293,c_1320]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_27,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(X1))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.68/2.99      | ~ v1_relat_1(X1) ),
% 19.68/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_491,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(X1))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 19.68/2.99      | k1_wellord2(X3) != X1 ),
% 19.68/2.99      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_492,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 19.68/2.99      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
% 19.68/2.99      inference(unflattening,[status(thm)],[c_491]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1289,plain,
% 19.68/2.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1319,plain,
% 19.68/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_1289,c_200]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_3840,plain,
% 19.68/2.99      ( r2_hidden(sK7(k1_wellord2(X0),X1),X0) = iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_1293,c_1319]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_15,plain,
% 19.68/2.99      ( ~ r2_hidden(X0,X1)
% 19.68/2.99      | ~ r2_hidden(X2,X3)
% 19.68/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f115]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1304,plain,
% 19.68/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.68/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.68/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_24,plain,
% 19.68/2.99      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
% 19.68/2.99      | r1_tarski(X0,X1)
% 19.68/2.99      | ~ v1_relat_1(X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_452,plain,
% 19.68/2.99      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
% 19.68/2.99      | r1_tarski(X0,X1)
% 19.68/2.99      | k1_wellord2(X2) != X0 ),
% 19.68/2.99      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_453,plain,
% 19.68/2.99      ( ~ r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1)
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) ),
% 19.68/2.99      inference(unflattening,[status(thm)],[c_452]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1292,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1) != iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_3110,plain,
% 19.68/2.99      ( r2_hidden(sK7(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X2) != iProver_top
% 19.68/2.99      | r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X1) != iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_1304,c_1292]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_39134,plain,
% 19.68/2.99      ( r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) != iProver_top
% 19.68/2.99      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_3840,c_3110]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_40331,plain,
% 19.68/2.99      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_3837,c_39134]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_0,plain,
% 19.68/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.68/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1318,plain,
% 19.68/2.99      ( X0 = X1
% 19.68/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.68/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_40521,plain,
% 19.68/2.99      ( k2_zfmisc_1(X0,X0) = k1_wellord2(X0)
% 19.68/2.99      | r1_tarski(k2_zfmisc_1(X0,X0),k1_wellord2(X0)) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_40331,c_1318]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_40526,plain,
% 19.68/2.99      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k1_wellord2(k2_enumset1(X0,X0,X0,X0))
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 19.68/2.99      inference(superposition,[status(thm)],[c_3008,c_40521]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_40529,plain,
% 19.68/2.99      ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
% 19.68/2.99      | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) != iProver_top ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_40526]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_33,plain,
% 19.68/2.99      ( ~ r2_hidden(X0,X1)
% 19.68/2.99      | ~ r2_hidden(X2,X1)
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
% 19.68/2.99      | ~ r1_tarski(X0,X2)
% 19.68/2.99      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f123]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_519,plain,
% 19.68/2.99      ( ~ r2_hidden(X0,X1)
% 19.68/2.99      | ~ r2_hidden(X2,X1)
% 19.68/2.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
% 19.68/2.99      | ~ r1_tarski(X0,X2)
% 19.68/2.99      | k1_wellord2(X1) != k1_wellord2(X3) ),
% 19.68/2.99      inference(resolution_lifted,[status(thm)],[c_36,c_33]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1464,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
% 19.68/2.99      | ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
% 19.68/2.99      | ~ r1_tarski(sK10,sK10)
% 19.68/2.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(X0) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_519]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1775,plain,
% 19.68/2.99      ( r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
% 19.68/2.99      | ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
% 19.68/2.99      | ~ r1_tarski(sK10,sK10)
% 19.68/2.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_1464]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1776,plain,
% 19.68/2.99      ( k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
% 19.68/2.99      | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) = iProver_top
% 19.68/2.99      | r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) != iProver_top
% 19.68/2.99      | r1_tarski(sK10,sK10) != iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1,plain,
% 19.68/2.99      ( r1_tarski(X0,X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f105]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1756,plain,
% 19.68/2.99      ( r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1406,plain,
% 19.68/2.99      ( ~ r1_tarski(X0,k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
% 19.68/2.99      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),X0)
% 19.68/2.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = X0 ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1523,plain,
% 19.68/2.99      ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)))
% 19.68/2.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_37,negated_conjecture,
% 19.68/2.99      ( k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f104]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_1496,plain,
% 19.68/2.99      ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 19.68/2.99      inference(demodulation,[status(thm)],[c_37,c_20]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_2,plain,
% 19.68/2.99      ( r1_tarski(X0,X0) ),
% 19.68/2.99      inference(cnf_transformation,[],[f106]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_121,plain,
% 19.68/2.99      ( r1_tarski(X0,X0) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_123,plain,
% 19.68/2.99      ( r1_tarski(sK10,sK10) = iProver_top ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_9,plain,
% 19.68/2.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 19.68/2.99      inference(cnf_transformation,[],[f112]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_108,plain,
% 19.68/2.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 19.68/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(c_110,plain,
% 19.68/2.99      ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) = iProver_top ),
% 19.68/2.99      inference(instantiation,[status(thm)],[c_108]) ).
% 19.68/2.99  
% 19.68/2.99  cnf(contradiction,plain,
% 19.68/2.99      ( $false ),
% 19.68/2.99      inference(minisat,
% 19.68/2.99                [status(thm)],
% 19.68/2.99                [c_40529,c_1776,c_1756,c_1523,c_1496,c_123,c_110]) ).
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.68/2.99  
% 19.68/2.99  ------                               Statistics
% 19.68/2.99  
% 19.68/2.99  ------ General
% 19.68/2.99  
% 19.68/2.99  abstr_ref_over_cycles:                  0
% 19.68/2.99  abstr_ref_under_cycles:                 0
% 19.68/2.99  gc_basic_clause_elim:                   0
% 19.68/2.99  forced_gc_time:                         0
% 19.68/2.99  parsing_time:                           0.01
% 19.68/2.99  unif_index_cands_time:                  0.
% 19.68/2.99  unif_index_add_time:                    0.
% 19.68/2.99  orderings_time:                         0.
% 19.68/2.99  out_proof_time:                         0.01
% 19.68/2.99  total_time:                             2.207
% 19.68/2.99  num_of_symbols:                         50
% 19.68/2.99  num_of_terms:                           83040
% 19.68/2.99  
% 19.68/2.99  ------ Preprocessing
% 19.68/2.99  
% 19.68/2.99  num_of_splits:                          0
% 19.68/2.99  num_of_split_atoms:                     0
% 19.68/2.99  num_of_reused_defs:                     0
% 19.68/2.99  num_eq_ax_congr_red:                    67
% 19.68/2.99  num_of_sem_filtered_clauses:            1
% 19.68/2.99  num_of_subtypes:                        0
% 19.68/2.99  monotx_restored_types:                  0
% 19.68/2.99  sat_num_of_epr_types:                   0
% 19.68/2.99  sat_num_of_non_cyclic_types:            0
% 19.68/2.99  sat_guarded_non_collapsed_types:        0
% 19.68/2.99  num_pure_diseq_elim:                    0
% 19.68/2.99  simp_replaced_by:                       0
% 19.68/2.99  res_preprocessed:                       172
% 19.68/2.99  prep_upred:                             0
% 19.68/2.99  prep_unflattend:                        9
% 19.68/2.99  smt_new_axioms:                         0
% 19.68/2.99  pred_elim_cands:                        2
% 19.68/2.99  pred_elim:                              1
% 19.68/2.99  pred_elim_cl:                           1
% 19.68/2.99  pred_elim_cycles:                       3
% 19.68/2.99  merged_defs:                            0
% 19.68/2.99  merged_defs_ncl:                        0
% 19.68/2.99  bin_hyper_res:                          0
% 19.68/2.99  prep_cycles:                            4
% 19.68/2.99  pred_elim_time:                         0.005
% 19.68/2.99  splitting_time:                         0.
% 19.68/2.99  sem_filter_time:                        0.
% 19.68/2.99  monotx_time:                            0.
% 19.68/2.99  subtype_inf_time:                       0.
% 19.68/2.99  
% 19.68/2.99  ------ Problem properties
% 19.68/2.99  
% 19.68/2.99  clauses:                                36
% 19.68/2.99  conjectures:                            1
% 19.68/2.99  epr:                                    2
% 19.68/2.99  horn:                                   27
% 19.68/2.99  ground:                                 1
% 19.68/2.99  unary:                                  8
% 19.68/2.99  binary:                                 11
% 19.68/2.99  lits:                                   90
% 19.68/2.99  lits_eq:                                31
% 19.68/2.99  fd_pure:                                0
% 19.68/2.99  fd_pseudo:                              0
% 19.68/2.99  fd_cond:                                0
% 19.68/2.99  fd_pseudo_cond:                         9
% 19.68/2.99  ac_symbols:                             0
% 19.68/2.99  
% 19.68/2.99  ------ Propositional Solver
% 19.68/2.99  
% 19.68/2.99  prop_solver_calls:                      31
% 19.68/2.99  prop_fast_solver_calls:                 1241
% 19.68/2.99  smt_solver_calls:                       0
% 19.68/2.99  smt_fast_solver_calls:                  0
% 19.68/2.99  prop_num_of_clauses:                    15794
% 19.68/2.99  prop_preprocess_simplified:             28404
% 19.68/2.99  prop_fo_subsumed:                       3
% 19.68/2.99  prop_solver_time:                       0.
% 19.68/2.99  smt_solver_time:                        0.
% 19.68/2.99  smt_fast_solver_time:                   0.
% 19.68/2.99  prop_fast_solver_time:                  0.
% 19.68/2.99  prop_unsat_core_time:                   0.001
% 19.68/2.99  
% 19.68/2.99  ------ QBF
% 19.68/2.99  
% 19.68/2.99  qbf_q_res:                              0
% 19.68/2.99  qbf_num_tautologies:                    0
% 19.68/2.99  qbf_prep_cycles:                        0
% 19.68/2.99  
% 19.68/2.99  ------ BMC1
% 19.68/2.99  
% 19.68/2.99  bmc1_current_bound:                     -1
% 19.68/2.99  bmc1_last_solved_bound:                 -1
% 19.68/2.99  bmc1_unsat_core_size:                   -1
% 19.68/2.99  bmc1_unsat_core_parents_size:           -1
% 19.68/2.99  bmc1_merge_next_fun:                    0
% 19.68/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.68/2.99  
% 19.68/2.99  ------ Instantiation
% 19.68/2.99  
% 19.68/2.99  inst_num_of_clauses:                    3371
% 19.68/2.99  inst_num_in_passive:                    978
% 19.68/2.99  inst_num_in_active:                     889
% 19.68/2.99  inst_num_in_unprocessed:                1504
% 19.68/2.99  inst_num_of_loops:                      970
% 19.68/2.99  inst_num_of_learning_restarts:          0
% 19.68/2.99  inst_num_moves_active_passive:          77
% 19.68/2.99  inst_lit_activity:                      0
% 19.68/2.99  inst_lit_activity_moves:                0
% 19.68/2.99  inst_num_tautologies:                   0
% 19.68/2.99  inst_num_prop_implied:                  0
% 19.68/2.99  inst_num_existing_simplified:           0
% 19.68/2.99  inst_num_eq_res_simplified:             0
% 19.68/2.99  inst_num_child_elim:                    0
% 19.68/2.99  inst_num_of_dismatching_blockings:      4985
% 19.68/2.99  inst_num_of_non_proper_insts:           3659
% 19.68/2.99  inst_num_of_duplicates:                 0
% 19.68/2.99  inst_inst_num_from_inst_to_res:         0
% 19.68/2.99  inst_dismatching_checking_time:         0.
% 19.68/2.99  
% 19.68/2.99  ------ Resolution
% 19.68/2.99  
% 19.68/2.99  res_num_of_clauses:                     0
% 19.68/2.99  res_num_in_passive:                     0
% 19.68/2.99  res_num_in_active:                      0
% 19.68/2.99  res_num_of_loops:                       176
% 19.68/2.99  res_forward_subset_subsumed:            879
% 19.68/2.99  res_backward_subset_subsumed:           6
% 19.68/2.99  res_forward_subsumed:                   0
% 19.68/2.99  res_backward_subsumed:                  0
% 19.68/2.99  res_forward_subsumption_resolution:     0
% 19.68/2.99  res_backward_subsumption_resolution:    0
% 19.68/2.99  res_clause_to_clause_subsumption:       33883
% 19.68/2.99  res_orphan_elimination:                 0
% 19.68/2.99  res_tautology_del:                      223
% 19.68/2.99  res_num_eq_res_simplified:              0
% 19.68/2.99  res_num_sel_changes:                    0
% 19.68/2.99  res_moves_from_active_to_pass:          0
% 19.68/2.99  
% 19.68/2.99  ------ Superposition
% 19.68/2.99  
% 19.68/2.99  sup_time_total:                         0.
% 19.68/2.99  sup_time_generating:                    0.
% 19.68/2.99  sup_time_sim_full:                      0.
% 19.68/2.99  sup_time_sim_immed:                     0.
% 19.68/2.99  
% 19.68/2.99  sup_num_of_clauses:                     2477
% 19.68/2.99  sup_num_in_active:                      184
% 19.68/2.99  sup_num_in_passive:                     2293
% 19.68/2.99  sup_num_of_loops:                       193
% 19.68/2.99  sup_fw_superposition:                   2792
% 19.68/2.99  sup_bw_superposition:                   2673
% 19.68/2.99  sup_immediate_simplified:               4378
% 19.68/2.99  sup_given_eliminated:                   0
% 19.68/2.99  comparisons_done:                       0
% 19.68/2.99  comparisons_avoided:                    8
% 19.68/2.99  
% 19.68/2.99  ------ Simplifications
% 19.68/2.99  
% 19.68/2.99  
% 19.68/2.99  sim_fw_subset_subsumed:                 5
% 19.68/2.99  sim_bw_subset_subsumed:                 0
% 19.68/2.99  sim_fw_subsumed:                        734
% 19.68/2.99  sim_bw_subsumed:                        2
% 19.68/2.99  sim_fw_subsumption_res:                 0
% 19.68/2.99  sim_bw_subsumption_res:                 0
% 19.68/2.99  sim_tautology_del:                      14
% 19.68/2.99  sim_eq_tautology_del:                   509
% 19.68/2.99  sim_eq_res_simp:                        0
% 19.68/2.99  sim_fw_demodulated:                     4230
% 19.68/2.99  sim_bw_demodulated:                     524
% 19.68/2.99  sim_light_normalised:                   162
% 19.68/2.99  sim_joinable_taut:                      0
% 19.68/2.99  sim_joinable_simp:                      0
% 19.68/2.99  sim_ac_normalised:                      0
% 19.68/2.99  sim_smt_subsumption:                    0
% 19.68/2.99  
%------------------------------------------------------------------------------
