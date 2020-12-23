%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0764+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:04 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  200 (1610 expanded)
%              Number of clauses        :  126 ( 414 expanded)
%              Number of leaves         :   20 ( 477 expanded)
%              Depth                    :   23
%              Number of atoms          :  838 (9589 expanded)
%              Number of equality atoms :  233 (1479 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1) )
     => ( ~ r2_hidden(k4_tarski(X2,sK9(X2)),X0)
        & r2_hidden(sK9(X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,sK8) )
            | ~ r2_hidden(X2,sK8) )
        & k1_xboole_0 != sK8
        & r1_tarski(sK8,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & r2_hidden(X3,X1) )
                | ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1
            & r1_tarski(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK7)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(sK7)) )
      & v2_wellord1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK9(X2)),sK7)
          & r2_hidden(sK9(X2),sK8) )
        | ~ r2_hidden(X2,sK8) )
    & k1_xboole_0 != sK8
    & r1_tarski(sK8,k3_relat_1(sK7))
    & v2_wellord1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f26,f52,f51,f50])).

fof(f90,plain,(
    r1_tarski(sK8,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,X1) )
              | k1_xboole_0 = X1
              | ~ r1_tarski(X1,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r1_xboole_0(k1_wellord1(X0,X4),X3)
                  & r2_hidden(X4,X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r1_xboole_0(k1_wellord1(X0,X4),X3)
          & r2_hidden(X4,X3) )
     => ( r1_xboole_0(k1_wellord1(X0,sK2(X0,X3)),X3)
        & r2_hidden(sK2(X0,X3),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK1(X0))
            | ~ r2_hidden(X2,sK1(X0)) )
        & k1_xboole_0 != sK1(X0)
        & r1_tarski(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ( ! [X2] :
                ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK1(X0))
                | ~ r2_hidden(X2,sK1(X0)) )
            & k1_xboole_0 != sK1(X0)
            & r1_tarski(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ( r1_xboole_0(k1_wellord1(X0,sK2(X0,X3)),X3)
                & r2_hidden(sK2(X0,X3),X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r1_xboole_0(k1_wellord1(X0,sK2(X0,X3)),X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
        & sK4(X0) != sK5(X0)
        & r2_hidden(sK5(X0),k3_relat_1(X0))
        & r2_hidden(sK4(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
            & sK4(X0) != sK5(X0)
            & r2_hidden(sK5(X0),k3_relat_1(X0))
            & r2_hidden(sK4(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f45])).

fof(f74,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK9(X2)),sK7)
      | ~ r2_hidden(X2,sK8) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK2(X0,X3),X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f48])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X2] :
      ( r2_hidden(sK9(X2),sK8)
      | ~ r2_hidden(X2,sK8) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f71,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(sK8,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_xboole_0(k1_wellord1(X1,sK2(X1,X0)),X0)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1571,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_xboole_0(k1_wellord1(X1,sK2(X1,X0)),X0)
    | ~ v1_wellord1(X1)
    | sK7 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_39])).

cnf(c_1572,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | ~ v1_wellord1(sK7)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1571])).

cnf(c_12,plain,
    ( ~ v2_wellord1(X0)
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,negated_conjecture,
    ( v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_564,plain,
    ( v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_565,plain,
    ( v1_wellord1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_567,plain,
    ( v1_wellord1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_39])).

cnf(c_1190,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_xboole_0(k1_wellord1(X1,sK2(X1,X0)),X0)
    | ~ v1_relat_1(X1)
    | sK7 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_567])).

cnf(c_1191,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | ~ v1_relat_1(sK7)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1190])).

cnf(c_1195,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK7))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1191,c_39])).

cnf(c_1196,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_1195])).

cnf(c_1576,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK7))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1572,c_39,c_1191])).

cnf(c_1577,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_1576])).

cnf(c_1775,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | k3_relat_1(sK7) != k3_relat_1(sK7)
    | sK8 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1577])).

cnf(c_1776,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,sK8)),sK8)
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_1775])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1193,plain,
    ( ~ r1_tarski(sK8,k3_relat_1(sK7))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,sK8)),sK8)
    | ~ v1_relat_1(sK7)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_1778,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,sK8)),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_39,c_37,c_36,c_1193])).

cnf(c_2570,plain,
    ( r1_xboole_0(k1_wellord1(sK7,sK2(sK7,sK8)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1515,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_1516,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | ~ r2_hidden(X1,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v6_relat_2(sK7)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1515])).

cnf(c_13,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_553,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_38])).

cnf(c_554,plain,
    ( v6_relat_2(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_556,plain,
    ( v6_relat_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_39])).

cnf(c_1384,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_556])).

cnf(c_1385,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | ~ r2_hidden(X1,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1384])).

cnf(c_1518,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7)
    | r2_hidden(k4_tarski(X1,X0),sK7)
    | ~ r2_hidden(X1,k3_relat_1(sK7))
    | ~ r2_hidden(X0,k3_relat_1(sK7))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1516,c_39,c_1385])).

cnf(c_1519,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | ~ r2_hidden(X1,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(k4_tarski(X0,X1),sK7)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1518])).

cnf(c_2579,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(k4_tarski(X0,sK9(X0)),sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2584,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9(X0)),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3590,plain,
    ( sK9(X0) = X0
    | r2_hidden(X0,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(k4_tarski(sK9(X0),X0),sK7) = iProver_top
    | r2_hidden(sK9(X0),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_2584])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1609,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_39])).

cnf(c_1610,plain,
    ( r2_hidden(X0,k1_wellord1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1609])).

cnf(c_2573,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK7,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1610])).

cnf(c_3781,plain,
    ( sK9(X0) = X0
    | r2_hidden(X0,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK9(X0),k1_wellord1(sK7,X0)) = iProver_top
    | r2_hidden(sK9(X0),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3590,c_2573])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1552,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ v1_wellord1(X1)
    | sK7 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_39])).

cnf(c_1553,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r2_hidden(sK2(sK7,X0),X0)
    | ~ v1_wellord1(sK7)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1552])).

cnf(c_1557,plain,
    ( r2_hidden(sK2(sK7,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK7))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1553,c_39,c_565])).

cnf(c_1558,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r2_hidden(sK2(sK7,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_1557])).

cnf(c_1786,plain,
    ( r2_hidden(sK2(sK7,X0),X0)
    | k3_relat_1(sK7) != k3_relat_1(sK7)
    | sK8 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1558])).

cnf(c_1787,plain,
    ( r2_hidden(sK2(sK7,sK8),sK8)
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_1786])).

cnf(c_1169,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ v1_relat_1(X1)
    | sK7 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_567])).

cnf(c_1170,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | r2_hidden(sK2(sK7,X0),X0)
    | ~ v1_relat_1(sK7)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_1172,plain,
    ( ~ r1_tarski(sK8,k3_relat_1(sK7))
    | r2_hidden(sK2(sK7,sK8),sK8)
    | ~ v1_relat_1(sK7)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1789,plain,
    ( r2_hidden(sK2(sK7,sK8),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_39,c_37,c_36,c_1172])).

cnf(c_2569,plain,
    ( r2_hidden(sK2(sK7,sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_312,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_390,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_33,c_313])).

cnf(c_1728,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k3_relat_1(sK7) != X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_37])).

cnf(c_1729,plain,
    ( ~ r2_hidden(X0,sK8)
    | ~ v1_xboole_0(k3_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_1728])).

cnf(c_2581,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k3_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_2845,plain,
    ( v1_xboole_0(k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_2581])).

cnf(c_1738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_relat_1(sK7) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_37])).

cnf(c_1739,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) ),
    inference(unflattening,[status(thm)],[c_1738])).

cnf(c_2580,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_32,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2586,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3846,plain,
    ( m1_subset_1(X0,k3_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2580,c_2586])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2590,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4053,plain,
    ( r2_hidden(X0,k3_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k3_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3846,c_2590])).

cnf(c_6086,plain,
    ( sK9(X0) = X0
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK9(X0),k1_wellord1(sK7,X0)) = iProver_top
    | r2_hidden(sK9(X0),k3_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3781,c_2845,c_4053])).

cnf(c_29,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2589,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6096,plain,
    ( sK9(X0) = X0
    | r1_xboole_0(k1_wellord1(sK7,X0),X1) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK9(X0),X1) != iProver_top
    | r2_hidden(sK9(X0),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6086,c_2589])).

cnf(c_8265,plain,
    ( sK9(sK2(sK7,sK8)) = sK2(sK7,sK8)
    | r2_hidden(sK2(sK7,sK8),sK8) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_6096])).

cnf(c_40,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( r1_tarski(sK8,k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_985,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_relat_1(sK7) != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_37])).

cnf(c_986,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_987,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_1171,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7,X0),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_1173,plain,
    ( k1_xboole_0 = sK8
    | r1_tarski(sK8,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7,sK8),sK8) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(sK9(X0),sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2750,plain,
    ( ~ r2_hidden(sK2(sK7,sK8),sK8)
    | r2_hidden(sK9(sK2(sK7,sK8)),sK8) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2751,plain,
    ( r2_hidden(sK2(sK7,sK8),sK8) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2750])).

cnf(c_2828,plain,
    ( m1_subset_1(sK9(sK2(sK7,sK8)),X0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK9(sK2(sK7,sK8)),sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2980,plain,
    ( m1_subset_1(sK9(sK2(sK7,sK8)),k3_relat_1(sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7)))
    | ~ r2_hidden(sK9(sK2(sK7,sK8)),sK8) ),
    inference(instantiation,[status(thm)],[c_2828])).

cnf(c_2981,plain,
    ( m1_subset_1(sK9(sK2(sK7,sK8)),k3_relat_1(sK7)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2980])).

cnf(c_3465,plain,
    ( ~ m1_subset_1(sK9(sK2(sK7,sK8)),k3_relat_1(sK7))
    | r2_hidden(sK9(sK2(sK7,sK8)),k3_relat_1(sK7))
    | v1_xboole_0(k3_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3466,plain,
    ( m1_subset_1(sK9(sK2(sK7,sK8)),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),k3_relat_1(sK7)) = iProver_top
    | v1_xboole_0(k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3465])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_310,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_1745,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X2)),X2)
    | X2 != X0
    | k3_relat_1(sK7) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_311,c_1577])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k3_relat_1(sK7)))
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1745])).

cnf(c_2572,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | r1_xboole_0(k1_wellord1(sK7,sK2(sK7,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1746])).

cnf(c_8264,plain,
    ( sK9(sK2(sK7,X0)) = sK2(sK7,X0)
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | r2_hidden(sK2(sK7,X0),sK8) != iProver_top
    | r2_hidden(sK9(sK2(sK7,X0)),X0) != iProver_top
    | r2_hidden(sK9(sK2(sK7,X0)),k3_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_6096])).

cnf(c_8287,plain,
    ( sK9(sK2(sK7,sK8)) = sK2(sK7,sK8)
    | k1_xboole_0 = sK8
    | m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | r2_hidden(sK2(sK7,sK8),sK8) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK9(sK2(sK7,sK8)),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8264])).

cnf(c_8474,plain,
    ( sK9(sK2(sK7,sK8)) = sK2(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8265,c_40,c_42,c_36,c_987,c_1173,c_2751,c_2845,c_2981,c_3466,c_8287])).

cnf(c_8486,plain,
    ( r2_hidden(sK2(sK7,sK8),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK7,sK8),sK2(sK7,sK8)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8474,c_2584])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1538,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_1539,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,X0),sK7)
    | ~ v1_relat_2(sK7) ),
    inference(unflattening,[status(thm)],[c_1538])).

cnf(c_16,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_542,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_543,plain,
    ( v1_relat_2(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_545,plain,
    ( v1_relat_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_39])).

cnf(c_617,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_545])).

cnf(c_618,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,X0),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK7)
    | ~ r2_hidden(X0,k3_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_39])).

cnf(c_623,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,X0),sK7) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_1541,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK7)
    | ~ r2_hidden(X0,k3_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_39,c_618])).

cnf(c_1542,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,X0),sK7) ),
    inference(renaming,[status(thm)],[c_1541])).

cnf(c_4287,plain,
    ( ~ r2_hidden(sK2(sK7,X0),k3_relat_1(sK7))
    | r2_hidden(k4_tarski(sK2(sK7,X0),sK2(sK7,X0)),sK7) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_4292,plain,
    ( r2_hidden(sK2(sK7,X0),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK7,X0),sK2(sK7,X0)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4287])).

cnf(c_4294,plain,
    ( r2_hidden(sK2(sK7,sK8),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK7,sK8),sK2(sK7,sK8)),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4292])).

cnf(c_4223,plain,
    ( ~ m1_subset_1(sK2(sK7,X0),k3_relat_1(sK7))
    | r2_hidden(sK2(sK7,X0),k3_relat_1(sK7))
    | v1_xboole_0(k3_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4224,plain,
    ( m1_subset_1(sK2(sK7,X0),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7,X0),k3_relat_1(sK7)) = iProver_top
    | v1_xboole_0(k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4223])).

cnf(c_4226,plain,
    ( m1_subset_1(sK2(sK7,sK8),k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7,sK8),k3_relat_1(sK7)) = iProver_top
    | v1_xboole_0(k3_relat_1(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4224])).

cnf(c_2796,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(sK7,X0),X1)
    | ~ r2_hidden(sK2(sK7,X0),X0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k3_relat_1(sK7)))
    | m1_subset_1(sK2(sK7,X0),k3_relat_1(sK7))
    | ~ r2_hidden(sK2(sK7,X0),X0) ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_3249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | m1_subset_1(sK2(sK7,X0),k3_relat_1(sK7)) = iProver_top
    | r2_hidden(sK2(sK7,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3248])).

cnf(c_3251,plain,
    ( m1_subset_1(sK2(sK7,sK8),k3_relat_1(sK7)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k3_relat_1(sK7))) != iProver_top
    | r2_hidden(sK2(sK7,sK8),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3249])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8486,c_4294,c_4226,c_3251,c_2845,c_1173,c_987,c_36,c_42,c_40])).


%------------------------------------------------------------------------------
