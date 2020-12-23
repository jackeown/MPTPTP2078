%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:48 EST 2020

% Result     : Theorem 51.47s
% Output     : CNFRefutation 51.47s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 284 expanded)
%              Number of clauses        :   61 (  75 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  592 (1195 expanded)
%              Number of equality atoms :  261 ( 535 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f76,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f42,f43])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f112,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f99,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f72,f87,f87,f88])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f71,f87,f88,f87])).

fof(f13,conjecture,(
    ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,
    ( ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0))
   => k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f21,f45])).

fof(f86,plain,(
    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10)) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(definition_unfolding,[],[f86,f88,f88])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f108,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f109,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f108])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f110,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f96])).

cnf(c_24,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_504,plain,
    ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_505,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r1_tarski(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_1616,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_27,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_543,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_544,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1613,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_34,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_196,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_35])).

cnf(c_1664,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1613,c_196])).

cnf(c_4876,plain,
    ( r2_hidden(sK6(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_1664])).

cnf(c_26,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_555,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_556,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_1612,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1659,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1612,c_196])).

cnf(c_4879,plain,
    ( r2_hidden(sK7(k1_wellord2(X0),X1),X0) = iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_1659])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1626,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23,plain,
    ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_516,plain,
    ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_517,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1)
    | r1_tarski(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1615,plain,
    ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_3686,plain,
    ( r2_hidden(sK7(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X2) != iProver_top
    | r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1615])).

cnf(c_140631,plain,
    ( r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) != iProver_top
    | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4879,c_3686])).

cnf(c_143025,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4876,c_140631])).

cnf(c_21,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1622,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2167,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r1_tarski(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1622])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1640,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4147,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r1_tarski(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_1640])).

cnf(c_143066,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k1_wellord2(k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_143025,c_4147])).

cnf(c_143084,plain,
    ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
    | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_143066])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
    | ~ r1_tarski(X0,X2)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
    | ~ r1_tarski(X0,X2)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_35,c_32])).

cnf(c_1981,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | ~ r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(k4_tarski(X0,X3),k1_wellord2(k2_enumset1(X1,X1,X2,X0)))
    | ~ r1_tarski(X0,X3)
    | k1_wellord2(k2_enumset1(X1,X1,X2,X0)) != k1_wellord2(X4) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_4078,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | ~ r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(k4_tarski(X0,X3),k1_wellord2(k2_enumset1(X1,X1,X2,X0)))
    | ~ r1_tarski(X0,X3)
    | k1_wellord2(k2_enumset1(X1,X1,X2,X0)) != k1_wellord2(k2_enumset1(X1,X1,X2,X0)) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_4080,plain,
    ( k1_wellord2(k2_enumset1(X0,X0,X1,X2)) != k1_wellord2(k2_enumset1(X0,X0,X1,X2))
    | r2_hidden(X2,k2_enumset1(X0,X0,X1,X2)) != iProver_top
    | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),k1_wellord2(k2_enumset1(X0,X0,X1,X2))) = iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4078])).

cnf(c_4082,plain,
    ( k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
    | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) = iProver_top
    | r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4080])).

cnf(c_935,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_2040,plain,
    ( k2_enumset1(sK10,sK10,sK10,sK10) != X0
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_2204,plain,
    ( k2_enumset1(sK10,sK10,sK10,sK10) != k2_enumset1(sK10,sK10,sK10,sK10)
    | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_22,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_36,negated_conjecture,
    ( k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1732,plain,
    ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(demodulation,[status(thm)],[c_22,c_36])).

cnf(c_928,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_939,plain,
    ( k2_enumset1(sK10,sK10,sK10,sK10) = k2_enumset1(sK10,sK10,sK10,sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_119,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_121,plain,
    ( r1_tarski(sK10,sK10) = iProver_top ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_106,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_108,plain,
    ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_107,plain,
    ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_104,plain,
    ( ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143084,c_4082,c_2204,c_1732,c_939,c_121,c_108,c_107,c_104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.47/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.47/6.99  
% 51.47/6.99  ------  iProver source info
% 51.47/6.99  
% 51.47/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.47/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.47/6.99  git: non_committed_changes: false
% 51.47/6.99  git: last_make_outside_of_git: false
% 51.47/6.99  
% 51.47/6.99  ------ 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options
% 51.47/6.99  
% 51.47/6.99  --out_options                           all
% 51.47/6.99  --tptp_safe_out                         true
% 51.47/6.99  --problem_path                          ""
% 51.47/6.99  --include_path                          ""
% 51.47/6.99  --clausifier                            res/vclausify_rel
% 51.47/6.99  --clausifier_options                    --mode clausify
% 51.47/6.99  --stdin                                 false
% 51.47/6.99  --stats_out                             all
% 51.47/6.99  
% 51.47/6.99  ------ General Options
% 51.47/6.99  
% 51.47/6.99  --fof                                   false
% 51.47/6.99  --time_out_real                         305.
% 51.47/6.99  --time_out_virtual                      -1.
% 51.47/6.99  --symbol_type_check                     false
% 51.47/6.99  --clausify_out                          false
% 51.47/6.99  --sig_cnt_out                           false
% 51.47/6.99  --trig_cnt_out                          false
% 51.47/6.99  --trig_cnt_out_tolerance                1.
% 51.47/6.99  --trig_cnt_out_sk_spl                   false
% 51.47/6.99  --abstr_cl_out                          false
% 51.47/6.99  
% 51.47/6.99  ------ Global Options
% 51.47/6.99  
% 51.47/6.99  --schedule                              default
% 51.47/6.99  --add_important_lit                     false
% 51.47/6.99  --prop_solver_per_cl                    1000
% 51.47/6.99  --min_unsat_core                        false
% 51.47/6.99  --soft_assumptions                      false
% 51.47/6.99  --soft_lemma_size                       3
% 51.47/6.99  --prop_impl_unit_size                   0
% 51.47/6.99  --prop_impl_unit                        []
% 51.47/6.99  --share_sel_clauses                     true
% 51.47/6.99  --reset_solvers                         false
% 51.47/6.99  --bc_imp_inh                            [conj_cone]
% 51.47/6.99  --conj_cone_tolerance                   3.
% 51.47/6.99  --extra_neg_conj                        none
% 51.47/6.99  --large_theory_mode                     true
% 51.47/6.99  --prolific_symb_bound                   200
% 51.47/6.99  --lt_threshold                          2000
% 51.47/6.99  --clause_weak_htbl                      true
% 51.47/6.99  --gc_record_bc_elim                     false
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing Options
% 51.47/6.99  
% 51.47/6.99  --preprocessing_flag                    true
% 51.47/6.99  --time_out_prep_mult                    0.1
% 51.47/6.99  --splitting_mode                        input
% 51.47/6.99  --splitting_grd                         true
% 51.47/6.99  --splitting_cvd                         false
% 51.47/6.99  --splitting_cvd_svl                     false
% 51.47/6.99  --splitting_nvd                         32
% 51.47/6.99  --sub_typing                            true
% 51.47/6.99  --prep_gs_sim                           true
% 51.47/6.99  --prep_unflatten                        true
% 51.47/6.99  --prep_res_sim                          true
% 51.47/6.99  --prep_upred                            true
% 51.47/6.99  --prep_sem_filter                       exhaustive
% 51.47/6.99  --prep_sem_filter_out                   false
% 51.47/6.99  --pred_elim                             true
% 51.47/6.99  --res_sim_input                         true
% 51.47/6.99  --eq_ax_congr_red                       true
% 51.47/6.99  --pure_diseq_elim                       true
% 51.47/6.99  --brand_transform                       false
% 51.47/6.99  --non_eq_to_eq                          false
% 51.47/6.99  --prep_def_merge                        true
% 51.47/6.99  --prep_def_merge_prop_impl              false
% 51.47/6.99  --prep_def_merge_mbd                    true
% 51.47/6.99  --prep_def_merge_tr_red                 false
% 51.47/6.99  --prep_def_merge_tr_cl                  false
% 51.47/6.99  --smt_preprocessing                     true
% 51.47/6.99  --smt_ac_axioms                         fast
% 51.47/6.99  --preprocessed_out                      false
% 51.47/6.99  --preprocessed_stats                    false
% 51.47/6.99  
% 51.47/6.99  ------ Abstraction refinement Options
% 51.47/6.99  
% 51.47/6.99  --abstr_ref                             []
% 51.47/6.99  --abstr_ref_prep                        false
% 51.47/6.99  --abstr_ref_until_sat                   false
% 51.47/6.99  --abstr_ref_sig_restrict                funpre
% 51.47/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.47/6.99  --abstr_ref_under                       []
% 51.47/6.99  
% 51.47/6.99  ------ SAT Options
% 51.47/6.99  
% 51.47/6.99  --sat_mode                              false
% 51.47/6.99  --sat_fm_restart_options                ""
% 51.47/6.99  --sat_gr_def                            false
% 51.47/6.99  --sat_epr_types                         true
% 51.47/6.99  --sat_non_cyclic_types                  false
% 51.47/6.99  --sat_finite_models                     false
% 51.47/6.99  --sat_fm_lemmas                         false
% 51.47/6.99  --sat_fm_prep                           false
% 51.47/6.99  --sat_fm_uc_incr                        true
% 51.47/6.99  --sat_out_model                         small
% 51.47/6.99  --sat_out_clauses                       false
% 51.47/6.99  
% 51.47/6.99  ------ QBF Options
% 51.47/6.99  
% 51.47/6.99  --qbf_mode                              false
% 51.47/6.99  --qbf_elim_univ                         false
% 51.47/6.99  --qbf_dom_inst                          none
% 51.47/6.99  --qbf_dom_pre_inst                      false
% 51.47/6.99  --qbf_sk_in                             false
% 51.47/6.99  --qbf_pred_elim                         true
% 51.47/6.99  --qbf_split                             512
% 51.47/6.99  
% 51.47/6.99  ------ BMC1 Options
% 51.47/6.99  
% 51.47/6.99  --bmc1_incremental                      false
% 51.47/6.99  --bmc1_axioms                           reachable_all
% 51.47/6.99  --bmc1_min_bound                        0
% 51.47/6.99  --bmc1_max_bound                        -1
% 51.47/6.99  --bmc1_max_bound_default                -1
% 51.47/6.99  --bmc1_symbol_reachability              true
% 51.47/6.99  --bmc1_property_lemmas                  false
% 51.47/6.99  --bmc1_k_induction                      false
% 51.47/6.99  --bmc1_non_equiv_states                 false
% 51.47/6.99  --bmc1_deadlock                         false
% 51.47/6.99  --bmc1_ucm                              false
% 51.47/6.99  --bmc1_add_unsat_core                   none
% 51.47/6.99  --bmc1_unsat_core_children              false
% 51.47/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.47/6.99  --bmc1_out_stat                         full
% 51.47/6.99  --bmc1_ground_init                      false
% 51.47/6.99  --bmc1_pre_inst_next_state              false
% 51.47/6.99  --bmc1_pre_inst_state                   false
% 51.47/6.99  --bmc1_pre_inst_reach_state             false
% 51.47/6.99  --bmc1_out_unsat_core                   false
% 51.47/6.99  --bmc1_aig_witness_out                  false
% 51.47/6.99  --bmc1_verbose                          false
% 51.47/6.99  --bmc1_dump_clauses_tptp                false
% 51.47/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.47/6.99  --bmc1_dump_file                        -
% 51.47/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.47/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.47/6.99  --bmc1_ucm_extend_mode                  1
% 51.47/6.99  --bmc1_ucm_init_mode                    2
% 51.47/6.99  --bmc1_ucm_cone_mode                    none
% 51.47/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.47/6.99  --bmc1_ucm_relax_model                  4
% 51.47/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.47/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.47/6.99  --bmc1_ucm_layered_model                none
% 51.47/6.99  --bmc1_ucm_max_lemma_size               10
% 51.47/6.99  
% 51.47/6.99  ------ AIG Options
% 51.47/6.99  
% 51.47/6.99  --aig_mode                              false
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation Options
% 51.47/6.99  
% 51.47/6.99  --instantiation_flag                    true
% 51.47/6.99  --inst_sos_flag                         false
% 51.47/6.99  --inst_sos_phase                        true
% 51.47/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel_side                     num_symb
% 51.47/6.99  --inst_solver_per_active                1400
% 51.47/6.99  --inst_solver_calls_frac                1.
% 51.47/6.99  --inst_passive_queue_type               priority_queues
% 51.47/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.47/6.99  --inst_passive_queues_freq              [25;2]
% 51.47/6.99  --inst_dismatching                      true
% 51.47/6.99  --inst_eager_unprocessed_to_passive     true
% 51.47/6.99  --inst_prop_sim_given                   true
% 51.47/6.99  --inst_prop_sim_new                     false
% 51.47/6.99  --inst_subs_new                         false
% 51.47/6.99  --inst_eq_res_simp                      false
% 51.47/6.99  --inst_subs_given                       false
% 51.47/6.99  --inst_orphan_elimination               true
% 51.47/6.99  --inst_learning_loop_flag               true
% 51.47/6.99  --inst_learning_start                   3000
% 51.47/6.99  --inst_learning_factor                  2
% 51.47/6.99  --inst_start_prop_sim_after_learn       3
% 51.47/6.99  --inst_sel_renew                        solver
% 51.47/6.99  --inst_lit_activity_flag                true
% 51.47/6.99  --inst_restr_to_given                   false
% 51.47/6.99  --inst_activity_threshold               500
% 51.47/6.99  --inst_out_proof                        true
% 51.47/6.99  
% 51.47/6.99  ------ Resolution Options
% 51.47/6.99  
% 51.47/6.99  --resolution_flag                       true
% 51.47/6.99  --res_lit_sel                           adaptive
% 51.47/6.99  --res_lit_sel_side                      none
% 51.47/6.99  --res_ordering                          kbo
% 51.47/6.99  --res_to_prop_solver                    active
% 51.47/6.99  --res_prop_simpl_new                    false
% 51.47/6.99  --res_prop_simpl_given                  true
% 51.47/6.99  --res_passive_queue_type                priority_queues
% 51.47/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.47/6.99  --res_passive_queues_freq               [15;5]
% 51.47/6.99  --res_forward_subs                      full
% 51.47/6.99  --res_backward_subs                     full
% 51.47/6.99  --res_forward_subs_resolution           true
% 51.47/6.99  --res_backward_subs_resolution          true
% 51.47/6.99  --res_orphan_elimination                true
% 51.47/6.99  --res_time_limit                        2.
% 51.47/6.99  --res_out_proof                         true
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Options
% 51.47/6.99  
% 51.47/6.99  --superposition_flag                    true
% 51.47/6.99  --sup_passive_queue_type                priority_queues
% 51.47/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.47/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.47/6.99  --demod_completeness_check              fast
% 51.47/6.99  --demod_use_ground                      true
% 51.47/6.99  --sup_to_prop_solver                    passive
% 51.47/6.99  --sup_prop_simpl_new                    true
% 51.47/6.99  --sup_prop_simpl_given                  true
% 51.47/6.99  --sup_fun_splitting                     false
% 51.47/6.99  --sup_smt_interval                      50000
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Simplification Setup
% 51.47/6.99  
% 51.47/6.99  --sup_indices_passive                   []
% 51.47/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.47/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_full_bw                           [BwDemod]
% 51.47/6.99  --sup_immed_triv                        [TrivRules]
% 51.47/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_immed_bw_main                     []
% 51.47/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.47/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.47/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.47/6.99  
% 51.47/6.99  ------ Combination Options
% 51.47/6.99  
% 51.47/6.99  --comb_res_mult                         3
% 51.47/6.99  --comb_sup_mult                         2
% 51.47/6.99  --comb_inst_mult                        10
% 51.47/6.99  
% 51.47/6.99  ------ Debug Options
% 51.47/6.99  
% 51.47/6.99  --dbg_backtrace                         false
% 51.47/6.99  --dbg_dump_prop_clauses                 false
% 51.47/6.99  --dbg_dump_prop_clauses_file            -
% 51.47/6.99  --dbg_out_stat                          false
% 51.47/6.99  ------ Parsing...
% 51.47/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.47/6.99  ------ Proving...
% 51.47/6.99  ------ Problem Properties 
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  clauses                                 35
% 51.47/6.99  conjectures                             1
% 51.47/6.99  EPR                                     2
% 51.47/6.99  Horn                                    26
% 51.47/6.99  unary                                   8
% 51.47/6.99  binary                                  11
% 51.47/6.99  lits                                    87
% 51.47/6.99  lits eq                                 31
% 51.47/6.99  fd_pure                                 0
% 51.47/6.99  fd_pseudo                               0
% 51.47/6.99  fd_cond                                 0
% 51.47/6.99  fd_pseudo_cond                          9
% 51.47/6.99  AC symbols                              0
% 51.47/6.99  
% 51.47/6.99  ------ Schedule dynamic 5 is on 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  ------ 
% 51.47/6.99  Current options:
% 51.47/6.99  ------ 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options
% 51.47/6.99  
% 51.47/6.99  --out_options                           all
% 51.47/6.99  --tptp_safe_out                         true
% 51.47/6.99  --problem_path                          ""
% 51.47/6.99  --include_path                          ""
% 51.47/6.99  --clausifier                            res/vclausify_rel
% 51.47/6.99  --clausifier_options                    --mode clausify
% 51.47/6.99  --stdin                                 false
% 51.47/6.99  --stats_out                             all
% 51.47/6.99  
% 51.47/6.99  ------ General Options
% 51.47/6.99  
% 51.47/6.99  --fof                                   false
% 51.47/6.99  --time_out_real                         305.
% 51.47/6.99  --time_out_virtual                      -1.
% 51.47/6.99  --symbol_type_check                     false
% 51.47/6.99  --clausify_out                          false
% 51.47/6.99  --sig_cnt_out                           false
% 51.47/6.99  --trig_cnt_out                          false
% 51.47/6.99  --trig_cnt_out_tolerance                1.
% 51.47/6.99  --trig_cnt_out_sk_spl                   false
% 51.47/6.99  --abstr_cl_out                          false
% 51.47/6.99  
% 51.47/6.99  ------ Global Options
% 51.47/6.99  
% 51.47/6.99  --schedule                              default
% 51.47/6.99  --add_important_lit                     false
% 51.47/6.99  --prop_solver_per_cl                    1000
% 51.47/6.99  --min_unsat_core                        false
% 51.47/6.99  --soft_assumptions                      false
% 51.47/6.99  --soft_lemma_size                       3
% 51.47/6.99  --prop_impl_unit_size                   0
% 51.47/6.99  --prop_impl_unit                        []
% 51.47/6.99  --share_sel_clauses                     true
% 51.47/6.99  --reset_solvers                         false
% 51.47/6.99  --bc_imp_inh                            [conj_cone]
% 51.47/6.99  --conj_cone_tolerance                   3.
% 51.47/6.99  --extra_neg_conj                        none
% 51.47/6.99  --large_theory_mode                     true
% 51.47/6.99  --prolific_symb_bound                   200
% 51.47/6.99  --lt_threshold                          2000
% 51.47/6.99  --clause_weak_htbl                      true
% 51.47/6.99  --gc_record_bc_elim                     false
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing Options
% 51.47/6.99  
% 51.47/6.99  --preprocessing_flag                    true
% 51.47/6.99  --time_out_prep_mult                    0.1
% 51.47/6.99  --splitting_mode                        input
% 51.47/6.99  --splitting_grd                         true
% 51.47/6.99  --splitting_cvd                         false
% 51.47/6.99  --splitting_cvd_svl                     false
% 51.47/6.99  --splitting_nvd                         32
% 51.47/6.99  --sub_typing                            true
% 51.47/6.99  --prep_gs_sim                           true
% 51.47/6.99  --prep_unflatten                        true
% 51.47/6.99  --prep_res_sim                          true
% 51.47/6.99  --prep_upred                            true
% 51.47/6.99  --prep_sem_filter                       exhaustive
% 51.47/6.99  --prep_sem_filter_out                   false
% 51.47/6.99  --pred_elim                             true
% 51.47/6.99  --res_sim_input                         true
% 51.47/6.99  --eq_ax_congr_red                       true
% 51.47/6.99  --pure_diseq_elim                       true
% 51.47/6.99  --brand_transform                       false
% 51.47/6.99  --non_eq_to_eq                          false
% 51.47/6.99  --prep_def_merge                        true
% 51.47/6.99  --prep_def_merge_prop_impl              false
% 51.47/6.99  --prep_def_merge_mbd                    true
% 51.47/6.99  --prep_def_merge_tr_red                 false
% 51.47/6.99  --prep_def_merge_tr_cl                  false
% 51.47/6.99  --smt_preprocessing                     true
% 51.47/6.99  --smt_ac_axioms                         fast
% 51.47/6.99  --preprocessed_out                      false
% 51.47/6.99  --preprocessed_stats                    false
% 51.47/6.99  
% 51.47/6.99  ------ Abstraction refinement Options
% 51.47/6.99  
% 51.47/6.99  --abstr_ref                             []
% 51.47/6.99  --abstr_ref_prep                        false
% 51.47/6.99  --abstr_ref_until_sat                   false
% 51.47/6.99  --abstr_ref_sig_restrict                funpre
% 51.47/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.47/6.99  --abstr_ref_under                       []
% 51.47/6.99  
% 51.47/6.99  ------ SAT Options
% 51.47/6.99  
% 51.47/6.99  --sat_mode                              false
% 51.47/6.99  --sat_fm_restart_options                ""
% 51.47/6.99  --sat_gr_def                            false
% 51.47/6.99  --sat_epr_types                         true
% 51.47/6.99  --sat_non_cyclic_types                  false
% 51.47/6.99  --sat_finite_models                     false
% 51.47/6.99  --sat_fm_lemmas                         false
% 51.47/6.99  --sat_fm_prep                           false
% 51.47/6.99  --sat_fm_uc_incr                        true
% 51.47/6.99  --sat_out_model                         small
% 51.47/6.99  --sat_out_clauses                       false
% 51.47/6.99  
% 51.47/6.99  ------ QBF Options
% 51.47/6.99  
% 51.47/6.99  --qbf_mode                              false
% 51.47/6.99  --qbf_elim_univ                         false
% 51.47/6.99  --qbf_dom_inst                          none
% 51.47/6.99  --qbf_dom_pre_inst                      false
% 51.47/6.99  --qbf_sk_in                             false
% 51.47/6.99  --qbf_pred_elim                         true
% 51.47/6.99  --qbf_split                             512
% 51.47/6.99  
% 51.47/6.99  ------ BMC1 Options
% 51.47/6.99  
% 51.47/6.99  --bmc1_incremental                      false
% 51.47/6.99  --bmc1_axioms                           reachable_all
% 51.47/6.99  --bmc1_min_bound                        0
% 51.47/6.99  --bmc1_max_bound                        -1
% 51.47/6.99  --bmc1_max_bound_default                -1
% 51.47/6.99  --bmc1_symbol_reachability              true
% 51.47/6.99  --bmc1_property_lemmas                  false
% 51.47/6.99  --bmc1_k_induction                      false
% 51.47/6.99  --bmc1_non_equiv_states                 false
% 51.47/6.99  --bmc1_deadlock                         false
% 51.47/6.99  --bmc1_ucm                              false
% 51.47/6.99  --bmc1_add_unsat_core                   none
% 51.47/6.99  --bmc1_unsat_core_children              false
% 51.47/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.47/6.99  --bmc1_out_stat                         full
% 51.47/6.99  --bmc1_ground_init                      false
% 51.47/6.99  --bmc1_pre_inst_next_state              false
% 51.47/6.99  --bmc1_pre_inst_state                   false
% 51.47/6.99  --bmc1_pre_inst_reach_state             false
% 51.47/6.99  --bmc1_out_unsat_core                   false
% 51.47/6.99  --bmc1_aig_witness_out                  false
% 51.47/6.99  --bmc1_verbose                          false
% 51.47/6.99  --bmc1_dump_clauses_tptp                false
% 51.47/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.47/6.99  --bmc1_dump_file                        -
% 51.47/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.47/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.47/6.99  --bmc1_ucm_extend_mode                  1
% 51.47/6.99  --bmc1_ucm_init_mode                    2
% 51.47/6.99  --bmc1_ucm_cone_mode                    none
% 51.47/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.47/6.99  --bmc1_ucm_relax_model                  4
% 51.47/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.47/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.47/6.99  --bmc1_ucm_layered_model                none
% 51.47/6.99  --bmc1_ucm_max_lemma_size               10
% 51.47/6.99  
% 51.47/6.99  ------ AIG Options
% 51.47/6.99  
% 51.47/6.99  --aig_mode                              false
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation Options
% 51.47/6.99  
% 51.47/6.99  --instantiation_flag                    true
% 51.47/6.99  --inst_sos_flag                         false
% 51.47/6.99  --inst_sos_phase                        true
% 51.47/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel_side                     none
% 51.47/6.99  --inst_solver_per_active                1400
% 51.47/6.99  --inst_solver_calls_frac                1.
% 51.47/6.99  --inst_passive_queue_type               priority_queues
% 51.47/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.47/6.99  --inst_passive_queues_freq              [25;2]
% 51.47/6.99  --inst_dismatching                      true
% 51.47/6.99  --inst_eager_unprocessed_to_passive     true
% 51.47/6.99  --inst_prop_sim_given                   true
% 51.47/6.99  --inst_prop_sim_new                     false
% 51.47/6.99  --inst_subs_new                         false
% 51.47/6.99  --inst_eq_res_simp                      false
% 51.47/6.99  --inst_subs_given                       false
% 51.47/6.99  --inst_orphan_elimination               true
% 51.47/6.99  --inst_learning_loop_flag               true
% 51.47/6.99  --inst_learning_start                   3000
% 51.47/6.99  --inst_learning_factor                  2
% 51.47/6.99  --inst_start_prop_sim_after_learn       3
% 51.47/6.99  --inst_sel_renew                        solver
% 51.47/6.99  --inst_lit_activity_flag                true
% 51.47/6.99  --inst_restr_to_given                   false
% 51.47/6.99  --inst_activity_threshold               500
% 51.47/6.99  --inst_out_proof                        true
% 51.47/6.99  
% 51.47/6.99  ------ Resolution Options
% 51.47/6.99  
% 51.47/6.99  --resolution_flag                       false
% 51.47/6.99  --res_lit_sel                           adaptive
% 51.47/6.99  --res_lit_sel_side                      none
% 51.47/6.99  --res_ordering                          kbo
% 51.47/6.99  --res_to_prop_solver                    active
% 51.47/6.99  --res_prop_simpl_new                    false
% 51.47/6.99  --res_prop_simpl_given                  true
% 51.47/6.99  --res_passive_queue_type                priority_queues
% 51.47/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.47/6.99  --res_passive_queues_freq               [15;5]
% 51.47/6.99  --res_forward_subs                      full
% 51.47/6.99  --res_backward_subs                     full
% 51.47/6.99  --res_forward_subs_resolution           true
% 51.47/6.99  --res_backward_subs_resolution          true
% 51.47/6.99  --res_orphan_elimination                true
% 51.47/6.99  --res_time_limit                        2.
% 51.47/6.99  --res_out_proof                         true
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Options
% 51.47/6.99  
% 51.47/6.99  --superposition_flag                    true
% 51.47/6.99  --sup_passive_queue_type                priority_queues
% 51.47/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.47/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.47/6.99  --demod_completeness_check              fast
% 51.47/6.99  --demod_use_ground                      true
% 51.47/6.99  --sup_to_prop_solver                    passive
% 51.47/6.99  --sup_prop_simpl_new                    true
% 51.47/6.99  --sup_prop_simpl_given                  true
% 51.47/6.99  --sup_fun_splitting                     false
% 51.47/6.99  --sup_smt_interval                      50000
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Simplification Setup
% 51.47/6.99  
% 51.47/6.99  --sup_indices_passive                   []
% 51.47/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.47/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_full_bw                           [BwDemod]
% 51.47/6.99  --sup_immed_triv                        [TrivRules]
% 51.47/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_immed_bw_main                     []
% 51.47/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.47/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.47/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.47/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.47/6.99  
% 51.47/6.99  ------ Combination Options
% 51.47/6.99  
% 51.47/6.99  --comb_res_mult                         3
% 51.47/6.99  --comb_sup_mult                         2
% 51.47/6.99  --comb_inst_mult                        10
% 51.47/6.99  
% 51.47/6.99  ------ Debug Options
% 51.47/6.99  
% 51.47/6.99  --dbg_backtrace                         false
% 51.47/6.99  --dbg_dump_prop_clauses                 false
% 51.47/6.99  --dbg_dump_prop_clauses_file            -
% 51.47/6.99  --dbg_out_stat                          false
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  ------ Proving...
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  % SZS status Theorem for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  fof(f9,axiom,(
% 51.47/6.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f16,plain,(
% 51.47/6.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 51.47/6.99    inference(ennf_transformation,[],[f9])).
% 51.47/6.99  
% 51.47/6.99  fof(f36,plain,(
% 51.47/6.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 51.47/6.99    inference(nnf_transformation,[],[f16])).
% 51.47/6.99  
% 51.47/6.99  fof(f37,plain,(
% 51.47/6.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 51.47/6.99    inference(rectify,[],[f36])).
% 51.47/6.99  
% 51.47/6.99  fof(f38,plain,(
% 51.47/6.99    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f39,plain,(
% 51.47/6.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f38])).
% 51.47/6.99  
% 51.47/6.99  fof(f74,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f39])).
% 51.47/6.99  
% 51.47/6.99  fof(f12,axiom,(
% 51.47/6.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f85,plain,(
% 51.47/6.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 51.47/6.99    inference(cnf_transformation,[],[f12])).
% 51.47/6.99  
% 51.47/6.99  fof(f10,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f17,plain,(
% 51.47/6.99    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 51.47/6.99    inference(ennf_transformation,[],[f10])).
% 51.47/6.99  
% 51.47/6.99  fof(f18,plain,(
% 51.47/6.99    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 51.47/6.99    inference(flattening,[],[f17])).
% 51.47/6.99  
% 51.47/6.99  fof(f76,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f18])).
% 51.47/6.99  
% 51.47/6.99  fof(f11,axiom,(
% 51.47/6.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f19,plain,(
% 51.47/6.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(ennf_transformation,[],[f11])).
% 51.47/6.99  
% 51.47/6.99  fof(f20,plain,(
% 51.47/6.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(flattening,[],[f19])).
% 51.47/6.99  
% 51.47/6.99  fof(f40,plain,(
% 51.47/6.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(nnf_transformation,[],[f20])).
% 51.47/6.99  
% 51.47/6.99  fof(f41,plain,(
% 51.47/6.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(flattening,[],[f40])).
% 51.47/6.99  
% 51.47/6.99  fof(f42,plain,(
% 51.47/6.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(rectify,[],[f41])).
% 51.47/6.99  
% 51.47/6.99  fof(f43,plain,(
% 51.47/6.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK8(X0,X1),sK9(X0,X1)) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r1_tarski(sK8(X0,X1),sK9(X0,X1)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0)))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f44,plain,(
% 51.47/6.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK8(X0,X1),sK9(X0,X1)) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r1_tarski(sK8(X0,X1),sK9(X0,X1)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f42,f43])).
% 51.47/6.99  
% 51.47/6.99  fof(f78,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f44])).
% 51.47/6.99  
% 51.47/6.99  fof(f122,plain,(
% 51.47/6.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 51.47/6.99    inference(equality_resolution,[],[f78])).
% 51.47/6.99  
% 51.47/6.99  fof(f77,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f18])).
% 51.47/6.99  
% 51.47/6.99  fof(f6,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f29,plain,(
% 51.47/6.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 51.47/6.99    inference(nnf_transformation,[],[f6])).
% 51.47/6.99  
% 51.47/6.99  fof(f30,plain,(
% 51.47/6.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 51.47/6.99    inference(rectify,[],[f29])).
% 51.47/6.99  
% 51.47/6.99  fof(f33,plain,(
% 51.47/6.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f32,plain,(
% 51.47/6.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f31,plain,(
% 51.47/6.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f34,plain,(
% 51.47/6.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 51.47/6.99  
% 51.47/6.99  fof(f64,plain,(
% 51.47/6.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 51.47/6.99    inference(cnf_transformation,[],[f34])).
% 51.47/6.99  
% 51.47/6.99  fof(f111,plain,(
% 51.47/6.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 51.47/6.99    inference(equality_resolution,[],[f64])).
% 51.47/6.99  
% 51.47/6.99  fof(f112,plain,(
% 51.47/6.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 51.47/6.99    inference(equality_resolution,[],[f111])).
% 51.47/6.99  
% 51.47/6.99  fof(f75,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f39])).
% 51.47/6.99  
% 51.47/6.99  fof(f8,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f72,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 51.47/6.99    inference(cnf_transformation,[],[f8])).
% 51.47/6.99  
% 51.47/6.99  fof(f3,axiom,(
% 51.47/6.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f58,plain,(
% 51.47/6.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f3])).
% 51.47/6.99  
% 51.47/6.99  fof(f4,axiom,(
% 51.47/6.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f59,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f4])).
% 51.47/6.99  
% 51.47/6.99  fof(f5,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f60,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f5])).
% 51.47/6.99  
% 51.47/6.99  fof(f87,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 51.47/6.99    inference(definition_unfolding,[],[f59,f60])).
% 51.47/6.99  
% 51.47/6.99  fof(f88,plain,(
% 51.47/6.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 51.47/6.99    inference(definition_unfolding,[],[f58,f87])).
% 51.47/6.99  
% 51.47/6.99  fof(f99,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 51.47/6.99    inference(definition_unfolding,[],[f72,f87,f87,f88])).
% 51.47/6.99  
% 51.47/6.99  fof(f7,axiom,(
% 51.47/6.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f35,plain,(
% 51.47/6.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 51.47/6.99    inference(nnf_transformation,[],[f7])).
% 51.47/6.99  
% 51.47/6.99  fof(f70,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f35])).
% 51.47/6.99  
% 51.47/6.99  fof(f97,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.47/6.99    inference(definition_unfolding,[],[f70,f88])).
% 51.47/6.99  
% 51.47/6.99  fof(f1,axiom,(
% 51.47/6.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f22,plain,(
% 51.47/6.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.47/6.99    inference(nnf_transformation,[],[f1])).
% 51.47/6.99  
% 51.47/6.99  fof(f23,plain,(
% 51.47/6.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.47/6.99    inference(flattening,[],[f22])).
% 51.47/6.99  
% 51.47/6.99  fof(f49,plain,(
% 51.47/6.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f23])).
% 51.47/6.99  
% 51.47/6.99  fof(f80,plain,(
% 51.47/6.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f44])).
% 51.47/6.99  
% 51.47/6.99  fof(f120,plain,(
% 51.47/6.99    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 51.47/6.99    inference(equality_resolution,[],[f80])).
% 51.47/6.99  
% 51.47/6.99  fof(f71,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 51.47/6.99    inference(cnf_transformation,[],[f8])).
% 51.47/6.99  
% 51.47/6.99  fof(f100,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 51.47/6.99    inference(definition_unfolding,[],[f71,f87,f88,f87])).
% 51.47/6.99  
% 51.47/6.99  fof(f13,conjecture,(
% 51.47/6.99    ! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f14,negated_conjecture,(
% 51.47/6.99    ~! [X0] : k1_tarski(k4_tarski(X0,X0)) = k1_wellord2(k1_tarski(X0))),
% 51.47/6.99    inference(negated_conjecture,[],[f13])).
% 51.47/6.99  
% 51.47/6.99  fof(f21,plain,(
% 51.47/6.99    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0))),
% 51.47/6.99    inference(ennf_transformation,[],[f14])).
% 51.47/6.99  
% 51.47/6.99  fof(f45,plain,(
% 51.47/6.99    ? [X0] : k1_tarski(k4_tarski(X0,X0)) != k1_wellord2(k1_tarski(X0)) => k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f46,plain,(
% 51.47/6.99    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f21,f45])).
% 51.47/6.99  
% 51.47/6.99  fof(f86,plain,(
% 51.47/6.99    k1_tarski(k4_tarski(sK10,sK10)) != k1_wellord2(k1_tarski(sK10))),
% 51.47/6.99    inference(cnf_transformation,[],[f46])).
% 51.47/6.99  
% 51.47/6.99  fof(f101,plain,(
% 51.47/6.99    k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))),
% 51.47/6.99    inference(definition_unfolding,[],[f86,f88,f88])).
% 51.47/6.99  
% 51.47/6.99  fof(f47,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.47/6.99    inference(cnf_transformation,[],[f23])).
% 51.47/6.99  
% 51.47/6.99  fof(f103,plain,(
% 51.47/6.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.47/6.99    inference(equality_resolution,[],[f47])).
% 51.47/6.99  
% 51.47/6.99  fof(f2,axiom,(
% 51.47/6.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f15,plain,(
% 51.47/6.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 51.47/6.99    inference(ennf_transformation,[],[f2])).
% 51.47/6.99  
% 51.47/6.99  fof(f24,plain,(
% 51.47/6.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 51.47/6.99    inference(nnf_transformation,[],[f15])).
% 51.47/6.99  
% 51.47/6.99  fof(f25,plain,(
% 51.47/6.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 51.47/6.99    inference(flattening,[],[f24])).
% 51.47/6.99  
% 51.47/6.99  fof(f26,plain,(
% 51.47/6.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 51.47/6.99    inference(rectify,[],[f25])).
% 51.47/6.99  
% 51.47/6.99  fof(f27,plain,(
% 51.47/6.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f28,plain,(
% 51.47/6.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 51.47/6.99  
% 51.47/6.99  fof(f51,plain,(
% 51.47/6.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 51.47/6.99    inference(cnf_transformation,[],[f28])).
% 51.47/6.99  
% 51.47/6.99  fof(f95,plain,(
% 51.47/6.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 51.47/6.99    inference(definition_unfolding,[],[f51,f60])).
% 51.47/6.99  
% 51.47/6.99  fof(f108,plain,(
% 51.47/6.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 51.47/6.99    inference(equality_resolution,[],[f95])).
% 51.47/6.99  
% 51.47/6.99  fof(f109,plain,(
% 51.47/6.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 51.47/6.99    inference(equality_resolution,[],[f108])).
% 51.47/6.99  
% 51.47/6.99  fof(f50,plain,(
% 51.47/6.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 51.47/6.99    inference(cnf_transformation,[],[f28])).
% 51.47/6.99  
% 51.47/6.99  fof(f96,plain,(
% 51.47/6.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 51.47/6.99    inference(definition_unfolding,[],[f50,f60])).
% 51.47/6.99  
% 51.47/6.99  fof(f110,plain,(
% 51.47/6.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 51.47/6.99    inference(equality_resolution,[],[f96])).
% 51.47/6.99  
% 51.47/6.99  cnf(c_24,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
% 51.47/6.99      | r1_tarski(X0,X1)
% 51.47/6.99      | ~ v1_relat_1(X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f74]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_35,plain,
% 51.47/6.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f85]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_504,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
% 51.47/6.99      | r1_tarski(X0,X1)
% 51.47/6.99      | k1_wellord2(X2) != X0 ),
% 51.47/6.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_505,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0))
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) ),
% 51.47/6.99      inference(unflattening,[status(thm)],[c_504]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1616,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_27,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(X1))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 51.47/6.99      | ~ v1_relat_1(X1) ),
% 51.47/6.99      inference(cnf_transformation,[],[f76]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_543,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(X1))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 51.47/6.99      | k1_wellord2(X3) != X1 ),
% 51.47/6.99      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_544,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
% 51.47/6.99      inference(unflattening,[status(thm)],[c_543]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1613,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_34,plain,
% 51.47/6.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 51.47/6.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f122]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_196,plain,
% 51.47/6.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 51.47/6.99      inference(global_propositional_subsumption,
% 51.47/6.99                [status(thm)],
% 51.47/6.99                [c_34,c_35]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1664,plain,
% 51.47/6.99      ( r2_hidden(X0,X1) = iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_1613,c_196]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4876,plain,
% 51.47/6.99      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0) = iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_1616,c_1664]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_26,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(X1))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 51.47/6.99      | ~ v1_relat_1(X1) ),
% 51.47/6.99      inference(cnf_transformation,[],[f77]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_555,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(X1))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 51.47/6.99      | k1_wellord2(X3) != X1 ),
% 51.47/6.99      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_556,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 51.47/6.99      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
% 51.47/6.99      inference(unflattening,[status(thm)],[c_555]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1612,plain,
% 51.47/6.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1659,plain,
% 51.47/6.99      ( r2_hidden(X0,X1) = iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_1612,c_196]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4879,plain,
% 51.47/6.99      ( r2_hidden(sK7(k1_wellord2(X0),X1),X0) = iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_1616,c_1659]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_15,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,X1)
% 51.47/6.99      | ~ r2_hidden(X2,X3)
% 51.47/6.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f112]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1626,plain,
% 51.47/6.99      ( r2_hidden(X0,X1) != iProver_top
% 51.47/6.99      | r2_hidden(X2,X3) != iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_23,plain,
% 51.47/6.99      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
% 51.47/6.99      | r1_tarski(X0,X1)
% 51.47/6.99      | ~ v1_relat_1(X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f75]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_516,plain,
% 51.47/6.99      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
% 51.47/6.99      | r1_tarski(X0,X1)
% 51.47/6.99      | k1_wellord2(X2) != X0 ),
% 51.47/6.99      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_517,plain,
% 51.47/6.99      ( ~ r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1)
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) ),
% 51.47/6.99      inference(unflattening,[status(thm)],[c_516]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1615,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(sK6(k1_wellord2(X0),X1),sK7(k1_wellord2(X0),X1)),X1) != iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),X1) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_3686,plain,
% 51.47/6.99      ( r2_hidden(sK7(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X2) != iProver_top
% 51.47/6.99      | r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X2)),X1) != iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_1626,c_1615]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_140631,plain,
% 51.47/6.99      ( r2_hidden(sK6(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) != iProver_top
% 51.47/6.99      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4879,c_3686]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_143025,plain,
% 51.47/6.99      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4876,c_140631]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_21,plain,
% 51.47/6.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f99]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 51.47/6.99      inference(cnf_transformation,[],[f97]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1622,plain,
% 51.47/6.99      ( r2_hidden(X0,X1) != iProver_top
% 51.47/6.99      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2167,plain,
% 51.47/6.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 51.47/6.99      | r1_tarski(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_21,c_1622]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_0,plain,
% 51.47/6.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 51.47/6.99      inference(cnf_transformation,[],[f49]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1640,plain,
% 51.47/6.99      ( X0 = X1
% 51.47/6.99      | r1_tarski(X0,X1) != iProver_top
% 51.47/6.99      | r1_tarski(X1,X0) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4147,plain,
% 51.47/6.99      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = X2
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 51.47/6.99      | r1_tarski(X2,k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_2167,c_1640]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_143066,plain,
% 51.47/6.99      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) = k1_wellord2(k2_enumset1(X0,X0,X0,X0))
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_143025,c_4147]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_143084,plain,
% 51.47/6.99      ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
% 51.47/6.99      | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) != iProver_top ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_143066]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_32,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,X1)
% 51.47/6.99      | ~ r2_hidden(X2,X1)
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
% 51.47/6.99      | ~ r1_tarski(X0,X2)
% 51.47/6.99      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f120]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_583,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,X1)
% 51.47/6.99      | ~ r2_hidden(X2,X1)
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1))
% 51.47/6.99      | ~ r1_tarski(X0,X2)
% 51.47/6.99      | k1_wellord2(X1) != k1_wellord2(X3) ),
% 51.47/6.99      inference(resolution_lifted,[status(thm)],[c_35,c_32]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1981,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 51.47/6.99      | ~ r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X3),k1_wellord2(k2_enumset1(X1,X1,X2,X0)))
% 51.47/6.99      | ~ r1_tarski(X0,X3)
% 51.47/6.99      | k1_wellord2(k2_enumset1(X1,X1,X2,X0)) != k1_wellord2(X4) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_583]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4078,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 51.47/6.99      | ~ r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
% 51.47/6.99      | r2_hidden(k4_tarski(X0,X3),k1_wellord2(k2_enumset1(X1,X1,X2,X0)))
% 51.47/6.99      | ~ r1_tarski(X0,X3)
% 51.47/6.99      | k1_wellord2(k2_enumset1(X1,X1,X2,X0)) != k1_wellord2(k2_enumset1(X1,X1,X2,X0)) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_1981]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4080,plain,
% 51.47/6.99      ( k1_wellord2(k2_enumset1(X0,X0,X1,X2)) != k1_wellord2(k2_enumset1(X0,X0,X1,X2))
% 51.47/6.99      | r2_hidden(X2,k2_enumset1(X0,X0,X1,X2)) != iProver_top
% 51.47/6.99      | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top
% 51.47/6.99      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(k2_enumset1(X0,X0,X1,X2))) = iProver_top
% 51.47/6.99      | r1_tarski(X2,X3) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_4078]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4082,plain,
% 51.47/6.99      ( k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))
% 51.47/6.99      | r2_hidden(k4_tarski(sK10,sK10),k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10))) = iProver_top
% 51.47/6.99      | r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) != iProver_top
% 51.47/6.99      | r1_tarski(sK10,sK10) != iProver_top ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_4080]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_935,plain,
% 51.47/6.99      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 51.47/6.99      theory(equality) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2040,plain,
% 51.47/6.99      ( k2_enumset1(sK10,sK10,sK10,sK10) != X0
% 51.47/6.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(X0) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_935]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2204,plain,
% 51.47/6.99      ( k2_enumset1(sK10,sK10,sK10,sK10) != k2_enumset1(sK10,sK10,sK10,sK10)
% 51.47/6.99      | k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) = k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_2040]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_22,plain,
% 51.47/6.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f100]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_36,negated_conjecture,
% 51.47/6.99      ( k2_enumset1(k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10),k4_tarski(sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f101]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1732,plain,
% 51.47/6.99      ( k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK10,sK10,sK10,sK10)) != k1_wellord2(k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_22,c_36]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_928,plain,
% 51.47/6.99      ( X0 != X1
% 51.47/6.99      | X2 != X3
% 51.47/6.99      | X4 != X5
% 51.47/6.99      | X6 != X7
% 51.47/6.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 51.47/6.99      theory(equality) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_939,plain,
% 51.47/6.99      ( k2_enumset1(sK10,sK10,sK10,sK10) = k2_enumset1(sK10,sK10,sK10,sK10)
% 51.47/6.99      | sK10 != sK10 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_928]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2,plain,
% 51.47/6.99      ( r1_tarski(X0,X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f103]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_119,plain,
% 51.47/6.99      ( r1_tarski(X0,X0) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_121,plain,
% 51.47/6.99      ( r1_tarski(sK10,sK10) = iProver_top ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_119]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_9,plain,
% 51.47/6.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f109]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_106,plain,
% 51.47/6.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_108,plain,
% 51.47/6.99      ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) = iProver_top ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_106]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_107,plain,
% 51.47/6.99      ( r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10)) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_9]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_10,plain,
% 51.47/6.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 51.47/6.99      | X0 = X1
% 51.47/6.99      | X0 = X2
% 51.47/6.99      | X0 = X3 ),
% 51.47/6.99      inference(cnf_transformation,[],[f110]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_104,plain,
% 51.47/6.99      ( ~ r2_hidden(sK10,k2_enumset1(sK10,sK10,sK10,sK10))
% 51.47/6.99      | sK10 = sK10 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_10]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(contradiction,plain,
% 51.47/6.99      ( $false ),
% 51.47/6.99      inference(minisat,
% 51.47/6.99                [status(thm)],
% 51.47/6.99                [c_143084,c_4082,c_2204,c_1732,c_939,c_121,c_108,c_107,
% 51.47/6.99                 c_104]) ).
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  ------                               Statistics
% 51.47/6.99  
% 51.47/6.99  ------ General
% 51.47/6.99  
% 51.47/6.99  abstr_ref_over_cycles:                  0
% 51.47/6.99  abstr_ref_under_cycles:                 0
% 51.47/6.99  gc_basic_clause_elim:                   0
% 51.47/6.99  forced_gc_time:                         0
% 51.47/6.99  parsing_time:                           0.009
% 51.47/6.99  unif_index_cands_time:                  0.
% 51.47/6.99  unif_index_add_time:                    0.
% 51.47/6.99  orderings_time:                         0.
% 51.47/6.99  out_proof_time:                         0.014
% 51.47/6.99  total_time:                             6.12
% 51.47/6.99  num_of_symbols:                         50
% 51.47/6.99  num_of_terms:                           258299
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing
% 51.47/6.99  
% 51.47/6.99  num_of_splits:                          0
% 51.47/6.99  num_of_split_atoms:                     0
% 51.47/6.99  num_of_reused_defs:                     0
% 51.47/6.99  num_eq_ax_congr_red:                    67
% 51.47/6.99  num_of_sem_filtered_clauses:            1
% 51.47/6.99  num_of_subtypes:                        0
% 51.47/6.99  monotx_restored_types:                  0
% 51.47/6.99  sat_num_of_epr_types:                   0
% 51.47/6.99  sat_num_of_non_cyclic_types:            0
% 51.47/6.99  sat_guarded_non_collapsed_types:        0
% 51.47/6.99  num_pure_diseq_elim:                    0
% 51.47/6.99  simp_replaced_by:                       0
% 51.47/6.99  res_preprocessed:                       168
% 51.47/6.99  prep_upred:                             0
% 51.47/6.99  prep_unflattend:                        9
% 51.47/6.99  smt_new_axioms:                         0
% 51.47/6.99  pred_elim_cands:                        2
% 51.47/6.99  pred_elim:                              1
% 51.47/6.99  pred_elim_cl:                           1
% 51.47/6.99  pred_elim_cycles:                       3
% 51.47/6.99  merged_defs:                            8
% 51.47/6.99  merged_defs_ncl:                        0
% 51.47/6.99  bin_hyper_res:                          8
% 51.47/6.99  prep_cycles:                            4
% 51.47/6.99  pred_elim_time:                         0.004
% 51.47/6.99  splitting_time:                         0.
% 51.47/6.99  sem_filter_time:                        0.
% 51.47/6.99  monotx_time:                            0.001
% 51.47/6.99  subtype_inf_time:                       0.
% 51.47/6.99  
% 51.47/6.99  ------ Problem properties
% 51.47/6.99  
% 51.47/6.99  clauses:                                35
% 51.47/6.99  conjectures:                            1
% 51.47/6.99  epr:                                    2
% 51.47/6.99  horn:                                   26
% 51.47/6.99  ground:                                 1
% 51.47/6.99  unary:                                  8
% 51.47/6.99  binary:                                 11
% 51.47/6.99  lits:                                   87
% 51.47/6.99  lits_eq:                                31
% 51.47/6.99  fd_pure:                                0
% 51.47/6.99  fd_pseudo:                              0
% 51.47/6.99  fd_cond:                                0
% 51.47/6.99  fd_pseudo_cond:                         9
% 51.47/6.99  ac_symbols:                             0
% 51.47/6.99  
% 51.47/6.99  ------ Propositional Solver
% 51.47/6.99  
% 51.47/6.99  prop_solver_calls:                      38
% 51.47/6.99  prop_fast_solver_calls:                 1396
% 51.47/6.99  smt_solver_calls:                       0
% 51.47/6.99  smt_fast_solver_calls:                  0
% 51.47/6.99  prop_num_of_clauses:                    37453
% 51.47/6.99  prop_preprocess_simplified:             59981
% 51.47/6.99  prop_fo_subsumed:                       1
% 51.47/6.99  prop_solver_time:                       0.
% 51.47/6.99  smt_solver_time:                        0.
% 51.47/6.99  smt_fast_solver_time:                   0.
% 51.47/6.99  prop_fast_solver_time:                  0.
% 51.47/6.99  prop_unsat_core_time:                   0.003
% 51.47/6.99  
% 51.47/6.99  ------ QBF
% 51.47/6.99  
% 51.47/6.99  qbf_q_res:                              0
% 51.47/6.99  qbf_num_tautologies:                    0
% 51.47/6.99  qbf_prep_cycles:                        0
% 51.47/6.99  
% 51.47/6.99  ------ BMC1
% 51.47/6.99  
% 51.47/6.99  bmc1_current_bound:                     -1
% 51.47/6.99  bmc1_last_solved_bound:                 -1
% 51.47/6.99  bmc1_unsat_core_size:                   -1
% 51.47/6.99  bmc1_unsat_core_parents_size:           -1
% 51.47/6.99  bmc1_merge_next_fun:                    0
% 51.47/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation
% 51.47/6.99  
% 51.47/6.99  inst_num_of_clauses:                    6490
% 51.47/6.99  inst_num_in_passive:                    2163
% 51.47/6.99  inst_num_in_active:                     1296
% 51.47/6.99  inst_num_in_unprocessed:                3033
% 51.47/6.99  inst_num_of_loops:                      1620
% 51.47/6.99  inst_num_of_learning_restarts:          0
% 51.47/6.99  inst_num_moves_active_passive:          322
% 51.47/6.99  inst_lit_activity:                      0
% 51.47/6.99  inst_lit_activity_moves:                1
% 51.47/6.99  inst_num_tautologies:                   0
% 51.47/6.99  inst_num_prop_implied:                  0
% 51.47/6.99  inst_num_existing_simplified:           0
% 51.47/6.99  inst_num_eq_res_simplified:             0
% 51.47/6.99  inst_num_child_elim:                    0
% 51.47/6.99  inst_num_of_dismatching_blockings:      26780
% 51.47/6.99  inst_num_of_non_proper_insts:           10037
% 51.47/6.99  inst_num_of_duplicates:                 0
% 51.47/6.99  inst_inst_num_from_inst_to_res:         0
% 51.47/6.99  inst_dismatching_checking_time:         0.
% 51.47/6.99  
% 51.47/6.99  ------ Resolution
% 51.47/6.99  
% 51.47/6.99  res_num_of_clauses:                     0
% 51.47/6.99  res_num_in_passive:                     0
% 51.47/6.99  res_num_in_active:                      0
% 51.47/6.99  res_num_of_loops:                       172
% 51.47/6.99  res_forward_subset_subsumed:            1965
% 51.47/6.99  res_backward_subset_subsumed:           6
% 51.47/6.99  res_forward_subsumed:                   0
% 51.47/6.99  res_backward_subsumed:                  0
% 51.47/6.99  res_forward_subsumption_resolution:     0
% 51.47/6.99  res_backward_subsumption_resolution:    0
% 51.47/6.99  res_clause_to_clause_subsumption:       187692
% 51.47/6.99  res_orphan_elimination:                 0
% 51.47/6.99  res_tautology_del:                      499
% 51.47/6.99  res_num_eq_res_simplified:              0
% 51.47/6.99  res_num_sel_changes:                    0
% 51.47/6.99  res_moves_from_active_to_pass:          0
% 51.47/6.99  
% 51.47/6.99  ------ Superposition
% 51.47/6.99  
% 51.47/6.99  sup_time_total:                         0.
% 51.47/6.99  sup_time_generating:                    0.
% 51.47/6.99  sup_time_sim_full:                      0.
% 51.47/6.99  sup_time_sim_immed:                     0.
% 51.47/6.99  
% 51.47/6.99  sup_num_of_clauses:                     9692
% 51.47/6.99  sup_num_in_active:                      316
% 51.47/6.99  sup_num_in_passive:                     9376
% 51.47/6.99  sup_num_of_loops:                       323
% 51.47/6.99  sup_fw_superposition:                   9078
% 51.47/6.99  sup_bw_superposition:                   7529
% 51.47/6.99  sup_immediate_simplified:               11342
% 51.47/6.99  sup_given_eliminated:                   0
% 51.47/6.99  comparisons_done:                       0
% 51.47/6.99  comparisons_avoided:                    28
% 51.47/6.99  
% 51.47/6.99  ------ Simplifications
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  sim_fw_subset_subsumed:                 9
% 51.47/6.99  sim_bw_subset_subsumed:                 0
% 51.47/6.99  sim_fw_subsumed:                        1737
% 51.47/6.99  sim_bw_subsumed:                        6
% 51.47/6.99  sim_fw_subsumption_res:                 2
% 51.47/6.99  sim_bw_subsumption_res:                 1
% 51.47/6.99  sim_tautology_del:                      8
% 51.47/6.99  sim_eq_tautology_del:                   394
% 51.47/6.99  sim_eq_res_simp:                        0
% 51.47/6.99  sim_fw_demodulated:                     8488
% 51.47/6.99  sim_bw_demodulated:                     1384
% 51.47/6.99  sim_light_normalised:                   1388
% 51.47/6.99  sim_joinable_taut:                      0
% 51.47/6.99  sim_joinable_simp:                      0
% 51.47/6.99  sim_ac_normalised:                      0
% 51.47/6.99  sim_smt_subsumption:                    0
% 51.47/6.99  
%------------------------------------------------------------------------------
