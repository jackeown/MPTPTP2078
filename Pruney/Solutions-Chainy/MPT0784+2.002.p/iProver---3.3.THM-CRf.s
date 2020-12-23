%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:30 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 745 expanded)
%              Number of clauses        :  110 ( 212 expanded)
%              Number of leaves         :   20 ( 148 expanded)
%              Depth                    :   16
%              Number of atoms          :  747 (3331 expanded)
%              Number of equality atoms :  154 ( 382 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
      & v2_wellord1(sK11)
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    & v2_wellord1(sK11)
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f24,f50])).

fof(f87,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f40])).

fof(f73,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

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
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f9,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( ~ r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)
        & sK7(X0) != sK8(X0)
        & r2_hidden(sK8(X0),k3_relat_1(X0))
        & r2_hidden(sK7(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)
            & sK7(X0) != sK8(X0)
            & r2_hidden(sK8(X0),k3_relat_1(X0))
            & r2_hidden(sK7(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f48])).

fof(f81,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK5(X0) != sK6(X0)
        & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK5(X0) != sK6(X0)
            & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
            & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f44])).

fof(f77,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f13])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f58,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1371,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2248,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | X1 != k1_wellord1(sK11,sK10)
    | X0 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_4738,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,sK10))
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | X0 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_21191,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | r2_hidden(sK9,k1_wellord1(sK11,sK10))
    | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10)
    | sK9 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_4738])).

cnf(c_2243,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | X1 != k1_wellord1(sK11,sK9)
    | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_4722,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | k1_wellord1(X1,X2) != k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_7628,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r2_hidden(sK10,k1_wellord1(X0,X1))
    | k1_wellord1(X0,X1) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_4722])).

cnf(c_18394,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_7628])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_990,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_37])).

cnf(c_991,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_990])).

cnf(c_5795,plain,
    ( r2_hidden(k4_tarski(sK9,X0),sK11)
    | ~ r2_hidden(sK9,k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_12729,plain,
    ( r2_hidden(k4_tarski(sK9,sK10),sK11)
    | ~ r2_hidden(sK9,k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_5795])).

cnf(c_24,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1122,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_37])).

cnf(c_1123,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v8_relat_2(sK11) ),
    inference(unflattening,[status(thm)],[c_1122])).

cnf(c_19,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,negated_conjecture,
    ( v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_415,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_416,plain,
    ( v8_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_85,plain,
    ( v8_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_418,plain,
    ( v8_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_37,c_36,c_85])).

cnf(c_720,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_418])).

cnf(c_721,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_723,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_37])).

cnf(c_724,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_723])).

cnf(c_1125,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1123,c_37,c_721])).

cnf(c_1126,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_1125])).

cnf(c_3306,plain,
    ( r2_hidden(k4_tarski(X0,sK10),sK11)
    | ~ r2_hidden(k4_tarski(X0,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_12152,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) ),
    inference(instantiation,[status(thm)],[c_3306])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1000,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_37])).

cnf(c_1001,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1000])).

cnf(c_3902,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,sK9))
    | ~ r2_hidden(k4_tarski(X0,sK9),sK11)
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_10493,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK9),sK11)
    | r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK9))
    | sK9 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_3902])).

cnf(c_2063,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_6372,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
    | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
    | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_2486,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | r2_hidden(k4_tarski(X0,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK10,sK9),sK11) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_6203,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK10,sK9),sK11) ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_34,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_957,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_37])).

cnf(c_958,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v6_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_17,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_437,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_438,plain,
    ( v6_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_91,plain,
    ( v6_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_440,plain,
    ( v6_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_37,c_36,c_91])).

cnf(c_890,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_440])).

cnf(c_891,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_895,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_891,c_37])).

cnf(c_896,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_895])).

cnf(c_961,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_37,c_891])).

cnf(c_962,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_961])).

cnf(c_2057,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,sK10),sK11)
    | r2_hidden(k4_tarski(sK10,X0),sK11)
    | ~ r2_hidden(sK10,k3_relat_1(sK11))
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_4574,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11)
    | r2_hidden(k4_tarski(sK9,sK10),sK11)
    | ~ r2_hidden(sK10,k3_relat_1(sK11))
    | ~ r2_hidden(sK9,k3_relat_1(sK11))
    | sK10 = sK9 ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_1374,plain,
    ( X0 != X1
    | X2 != X3
    | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
    theory(equality)).

cnf(c_3059,plain,
    ( X0 != sK9
    | k1_wellord1(sK11,X0) = k1_wellord1(sK11,sK9)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_4126,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK9)
    | sK10 != sK9
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_3059])).

cnf(c_28,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1105,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_1106,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v4_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1105])).

cnf(c_18,plain,
    ( v4_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_426,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_427,plain,
    ( v4_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_88,plain,
    ( v4_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_429,plain,
    ( v4_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_37,c_36,c_88])).

cnf(c_624,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_429])).

cnf(c_625,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_1108,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_37,c_625])).

cnf(c_1109,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1108])).

cnf(c_2062,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK10,X0),sK11)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_3315,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | sK10 = sK9 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_1368,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2905,plain,
    ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1369,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1721,plain,
    ( k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X0
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1805,plain,
    ( k1_wellord1(sK11,sK10) != k1_wellord1(X0,X1)
    | k1_wellord1(sK11,sK9) != k1_wellord1(X0,X1)
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_2702,plain,
    ( k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK9)
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10)
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_2520,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_2080,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_7,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1025,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_37])).

cnf(c_1026,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_1996,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | r2_hidden(sK10,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1964,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
    | r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1778,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_1773,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_1383,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,negated_conjecture,
    ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_472,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_35])).

cnf(c_473,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_538,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_473])).

cnf(c_539,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK9)) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_531,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_473])).

cnf(c_532,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_4,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_465,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_35])).

cnf(c_466,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_524,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_466])).

cnf(c_525,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_517,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_466])).

cnf(c_518,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_6,plain,
    ( r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_479,plain,
    ( k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_35])).

cnf(c_480,plain,
    ( k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK10) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21191,c_18394,c_12729,c_12152,c_10493,c_6372,c_6203,c_4574,c_4126,c_3315,c_2905,c_2702,c_2520,c_2080,c_1996,c_1964,c_1778,c_1773,c_1383,c_539,c_532,c_525,c_518,c_480])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 17:36:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.89/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/1.50  
% 7.89/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.50  
% 7.89/1.50  ------  iProver source info
% 7.89/1.50  
% 7.89/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.50  git: non_committed_changes: false
% 7.89/1.50  git: last_make_outside_of_git: false
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  
% 7.89/1.50  ------ Input Options
% 7.89/1.50  
% 7.89/1.50  --out_options                           all
% 7.89/1.50  --tptp_safe_out                         true
% 7.89/1.50  --problem_path                          ""
% 7.89/1.50  --include_path                          ""
% 7.89/1.50  --clausifier                            res/vclausify_rel
% 7.89/1.50  --clausifier_options                    ""
% 7.89/1.50  --stdin                                 false
% 7.89/1.50  --stats_out                             all
% 7.89/1.50  
% 7.89/1.50  ------ General Options
% 7.89/1.50  
% 7.89/1.50  --fof                                   false
% 7.89/1.50  --time_out_real                         305.
% 7.89/1.50  --time_out_virtual                      -1.
% 7.89/1.50  --symbol_type_check                     false
% 7.89/1.50  --clausify_out                          false
% 7.89/1.50  --sig_cnt_out                           false
% 7.89/1.50  --trig_cnt_out                          false
% 7.89/1.50  --trig_cnt_out_tolerance                1.
% 7.89/1.50  --trig_cnt_out_sk_spl                   false
% 7.89/1.50  --abstr_cl_out                          false
% 7.89/1.50  
% 7.89/1.50  ------ Global Options
% 7.89/1.50  
% 7.89/1.50  --schedule                              default
% 7.89/1.50  --add_important_lit                     false
% 7.89/1.50  --prop_solver_per_cl                    1000
% 7.89/1.50  --min_unsat_core                        false
% 7.89/1.50  --soft_assumptions                      false
% 7.89/1.50  --soft_lemma_size                       3
% 7.89/1.50  --prop_impl_unit_size                   0
% 7.89/1.50  --prop_impl_unit                        []
% 7.89/1.50  --share_sel_clauses                     true
% 7.89/1.50  --reset_solvers                         false
% 7.89/1.50  --bc_imp_inh                            [conj_cone]
% 7.89/1.50  --conj_cone_tolerance                   3.
% 7.89/1.50  --extra_neg_conj                        none
% 7.89/1.50  --large_theory_mode                     true
% 7.89/1.50  --prolific_symb_bound                   200
% 7.89/1.50  --lt_threshold                          2000
% 7.89/1.50  --clause_weak_htbl                      true
% 7.89/1.50  --gc_record_bc_elim                     false
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing Options
% 7.89/1.50  
% 7.89/1.50  --preprocessing_flag                    true
% 7.89/1.50  --time_out_prep_mult                    0.1
% 7.89/1.50  --splitting_mode                        input
% 7.89/1.50  --splitting_grd                         true
% 7.89/1.50  --splitting_cvd                         false
% 7.89/1.50  --splitting_cvd_svl                     false
% 7.89/1.50  --splitting_nvd                         32
% 7.89/1.50  --sub_typing                            true
% 7.89/1.50  --prep_gs_sim                           true
% 7.89/1.50  --prep_unflatten                        true
% 7.89/1.50  --prep_res_sim                          true
% 7.89/1.50  --prep_upred                            true
% 7.89/1.50  --prep_sem_filter                       exhaustive
% 7.89/1.50  --prep_sem_filter_out                   false
% 7.89/1.50  --pred_elim                             true
% 7.89/1.50  --res_sim_input                         true
% 7.89/1.50  --eq_ax_congr_red                       true
% 7.89/1.50  --pure_diseq_elim                       true
% 7.89/1.50  --brand_transform                       false
% 7.89/1.50  --non_eq_to_eq                          false
% 7.89/1.50  --prep_def_merge                        true
% 7.89/1.50  --prep_def_merge_prop_impl              false
% 7.89/1.50  --prep_def_merge_mbd                    true
% 7.89/1.50  --prep_def_merge_tr_red                 false
% 7.89/1.50  --prep_def_merge_tr_cl                  false
% 7.89/1.50  --smt_preprocessing                     true
% 7.89/1.50  --smt_ac_axioms                         fast
% 7.89/1.50  --preprocessed_out                      false
% 7.89/1.50  --preprocessed_stats                    false
% 7.89/1.50  
% 7.89/1.50  ------ Abstraction refinement Options
% 7.89/1.50  
% 7.89/1.50  --abstr_ref                             []
% 7.89/1.50  --abstr_ref_prep                        false
% 7.89/1.50  --abstr_ref_until_sat                   false
% 7.89/1.50  --abstr_ref_sig_restrict                funpre
% 7.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.50  --abstr_ref_under                       []
% 7.89/1.50  
% 7.89/1.50  ------ SAT Options
% 7.89/1.50  
% 7.89/1.50  --sat_mode                              false
% 7.89/1.50  --sat_fm_restart_options                ""
% 7.89/1.50  --sat_gr_def                            false
% 7.89/1.50  --sat_epr_types                         true
% 7.89/1.50  --sat_non_cyclic_types                  false
% 7.89/1.50  --sat_finite_models                     false
% 7.89/1.50  --sat_fm_lemmas                         false
% 7.89/1.50  --sat_fm_prep                           false
% 7.89/1.50  --sat_fm_uc_incr                        true
% 7.89/1.50  --sat_out_model                         small
% 7.89/1.50  --sat_out_clauses                       false
% 7.89/1.50  
% 7.89/1.50  ------ QBF Options
% 7.89/1.50  
% 7.89/1.50  --qbf_mode                              false
% 7.89/1.50  --qbf_elim_univ                         false
% 7.89/1.50  --qbf_dom_inst                          none
% 7.89/1.50  --qbf_dom_pre_inst                      false
% 7.89/1.50  --qbf_sk_in                             false
% 7.89/1.50  --qbf_pred_elim                         true
% 7.89/1.50  --qbf_split                             512
% 7.89/1.50  
% 7.89/1.50  ------ BMC1 Options
% 7.89/1.50  
% 7.89/1.50  --bmc1_incremental                      false
% 7.89/1.50  --bmc1_axioms                           reachable_all
% 7.89/1.50  --bmc1_min_bound                        0
% 7.89/1.50  --bmc1_max_bound                        -1
% 7.89/1.50  --bmc1_max_bound_default                -1
% 7.89/1.50  --bmc1_symbol_reachability              true
% 7.89/1.50  --bmc1_property_lemmas                  false
% 7.89/1.50  --bmc1_k_induction                      false
% 7.89/1.50  --bmc1_non_equiv_states                 false
% 7.89/1.50  --bmc1_deadlock                         false
% 7.89/1.50  --bmc1_ucm                              false
% 7.89/1.50  --bmc1_add_unsat_core                   none
% 7.89/1.50  --bmc1_unsat_core_children              false
% 7.89/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.50  --bmc1_out_stat                         full
% 7.89/1.50  --bmc1_ground_init                      false
% 7.89/1.50  --bmc1_pre_inst_next_state              false
% 7.89/1.50  --bmc1_pre_inst_state                   false
% 7.89/1.50  --bmc1_pre_inst_reach_state             false
% 7.89/1.50  --bmc1_out_unsat_core                   false
% 7.89/1.50  --bmc1_aig_witness_out                  false
% 7.89/1.50  --bmc1_verbose                          false
% 7.89/1.50  --bmc1_dump_clauses_tptp                false
% 7.89/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.50  --bmc1_dump_file                        -
% 7.89/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.50  --bmc1_ucm_extend_mode                  1
% 7.89/1.50  --bmc1_ucm_init_mode                    2
% 7.89/1.50  --bmc1_ucm_cone_mode                    none
% 7.89/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.50  --bmc1_ucm_relax_model                  4
% 7.89/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.50  --bmc1_ucm_layered_model                none
% 7.89/1.50  --bmc1_ucm_max_lemma_size               10
% 7.89/1.50  
% 7.89/1.50  ------ AIG Options
% 7.89/1.50  
% 7.89/1.50  --aig_mode                              false
% 7.89/1.50  
% 7.89/1.50  ------ Instantiation Options
% 7.89/1.50  
% 7.89/1.50  --instantiation_flag                    true
% 7.89/1.50  --inst_sos_flag                         true
% 7.89/1.50  --inst_sos_phase                        true
% 7.89/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.50  --inst_lit_sel_side                     num_symb
% 7.89/1.50  --inst_solver_per_active                1400
% 7.89/1.50  --inst_solver_calls_frac                1.
% 7.89/1.50  --inst_passive_queue_type               priority_queues
% 7.89/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.89/1.50  --inst_passive_queues_freq              [25;2]
% 7.89/1.50  --inst_dismatching                      true
% 7.89/1.50  --inst_eager_unprocessed_to_passive     true
% 7.89/1.50  --inst_prop_sim_given                   true
% 7.89/1.50  --inst_prop_sim_new                     false
% 7.89/1.50  --inst_subs_new                         false
% 7.89/1.50  --inst_eq_res_simp                      false
% 7.89/1.50  --inst_subs_given                       false
% 7.89/1.50  --inst_orphan_elimination               true
% 7.89/1.50  --inst_learning_loop_flag               true
% 7.89/1.50  --inst_learning_start                   3000
% 7.89/1.50  --inst_learning_factor                  2
% 7.89/1.50  --inst_start_prop_sim_after_learn       3
% 7.89/1.50  --inst_sel_renew                        solver
% 7.89/1.50  --inst_lit_activity_flag                true
% 7.89/1.50  --inst_restr_to_given                   false
% 7.89/1.50  --inst_activity_threshold               500
% 7.89/1.50  --inst_out_proof                        true
% 7.89/1.50  
% 7.89/1.50  ------ Resolution Options
% 7.89/1.50  
% 7.89/1.50  --resolution_flag                       true
% 7.89/1.50  --res_lit_sel                           adaptive
% 7.89/1.50  --res_lit_sel_side                      none
% 7.89/1.50  --res_ordering                          kbo
% 7.89/1.50  --res_to_prop_solver                    active
% 7.89/1.50  --res_prop_simpl_new                    false
% 7.89/1.50  --res_prop_simpl_given                  true
% 7.89/1.50  --res_passive_queue_type                priority_queues
% 7.89/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.89/1.50  --res_passive_queues_freq               [15;5]
% 7.89/1.50  --res_forward_subs                      full
% 7.89/1.50  --res_backward_subs                     full
% 7.89/1.50  --res_forward_subs_resolution           true
% 7.89/1.50  --res_backward_subs_resolution          true
% 7.89/1.50  --res_orphan_elimination                true
% 7.89/1.50  --res_time_limit                        2.
% 7.89/1.50  --res_out_proof                         true
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Options
% 7.89/1.50  
% 7.89/1.50  --superposition_flag                    true
% 7.89/1.50  --sup_passive_queue_type                priority_queues
% 7.89/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.50  --demod_completeness_check              fast
% 7.89/1.50  --demod_use_ground                      true
% 7.89/1.50  --sup_to_prop_solver                    passive
% 7.89/1.50  --sup_prop_simpl_new                    true
% 7.89/1.50  --sup_prop_simpl_given                  true
% 7.89/1.50  --sup_fun_splitting                     true
% 7.89/1.50  --sup_smt_interval                      50000
% 7.89/1.50  
% 7.89/1.50  ------ Superposition Simplification Setup
% 7.89/1.50  
% 7.89/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.89/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.89/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.89/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.89/1.50  --sup_immed_triv                        [TrivRules]
% 7.89/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.50  --sup_immed_bw_main                     []
% 7.89/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.89/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.50  --sup_input_bw                          []
% 7.89/1.50  
% 7.89/1.50  ------ Combination Options
% 7.89/1.50  
% 7.89/1.50  --comb_res_mult                         3
% 7.89/1.50  --comb_sup_mult                         2
% 7.89/1.50  --comb_inst_mult                        10
% 7.89/1.50  
% 7.89/1.50  ------ Debug Options
% 7.89/1.50  
% 7.89/1.50  --dbg_backtrace                         false
% 7.89/1.50  --dbg_dump_prop_clauses                 false
% 7.89/1.50  --dbg_dump_prop_clauses_file            -
% 7.89/1.50  --dbg_out_stat                          false
% 7.89/1.50  ------ Parsing...
% 7.89/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.50  ------ Proving...
% 7.89/1.50  ------ Problem Properties 
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  clauses                                 18
% 7.89/1.50  conjectures                             0
% 7.89/1.50  EPR                                     2
% 7.89/1.50  Horn                                    12
% 7.89/1.50  unary                                   5
% 7.89/1.50  binary                                  5
% 7.89/1.50  lits                                    42
% 7.89/1.50  lits eq                                 9
% 7.89/1.50  fd_pure                                 0
% 7.89/1.50  fd_pseudo                               0
% 7.89/1.50  fd_cond                                 0
% 7.89/1.50  fd_pseudo_cond                          5
% 7.89/1.50  AC symbols                              0
% 7.89/1.50  
% 7.89/1.50  ------ Schedule dynamic 5 is on 
% 7.89/1.50  
% 7.89/1.50  ------ no conjectures: strip conj schedule 
% 7.89/1.50  
% 7.89/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 7.89/1.50  
% 7.89/1.50  
% 7.89/1.50  ------ 
% 7.89/1.50  Current options:
% 7.89/1.50  ------ 
% 7.89/1.50  
% 7.89/1.50  ------ Input Options
% 7.89/1.50  
% 7.89/1.50  --out_options                           all
% 7.89/1.50  --tptp_safe_out                         true
% 7.89/1.50  --problem_path                          ""
% 7.89/1.50  --include_path                          ""
% 7.89/1.50  --clausifier                            res/vclausify_rel
% 7.89/1.50  --clausifier_options                    ""
% 7.89/1.50  --stdin                                 false
% 7.89/1.50  --stats_out                             all
% 7.89/1.50  
% 7.89/1.50  ------ General Options
% 7.89/1.50  
% 7.89/1.50  --fof                                   false
% 7.89/1.50  --time_out_real                         305.
% 7.89/1.50  --time_out_virtual                      -1.
% 7.89/1.50  --symbol_type_check                     false
% 7.89/1.50  --clausify_out                          false
% 7.89/1.50  --sig_cnt_out                           false
% 7.89/1.50  --trig_cnt_out                          false
% 7.89/1.50  --trig_cnt_out_tolerance                1.
% 7.89/1.50  --trig_cnt_out_sk_spl                   false
% 7.89/1.50  --abstr_cl_out                          false
% 7.89/1.50  
% 7.89/1.50  ------ Global Options
% 7.89/1.50  
% 7.89/1.50  --schedule                              default
% 7.89/1.50  --add_important_lit                     false
% 7.89/1.50  --prop_solver_per_cl                    1000
% 7.89/1.50  --min_unsat_core                        false
% 7.89/1.50  --soft_assumptions                      false
% 7.89/1.50  --soft_lemma_size                       3
% 7.89/1.50  --prop_impl_unit_size                   0
% 7.89/1.50  --prop_impl_unit                        []
% 7.89/1.50  --share_sel_clauses                     true
% 7.89/1.50  --reset_solvers                         false
% 7.89/1.50  --bc_imp_inh                            [conj_cone]
% 7.89/1.50  --conj_cone_tolerance                   3.
% 7.89/1.50  --extra_neg_conj                        none
% 7.89/1.50  --large_theory_mode                     true
% 7.89/1.50  --prolific_symb_bound                   200
% 7.89/1.50  --lt_threshold                          2000
% 7.89/1.50  --clause_weak_htbl                      true
% 7.89/1.50  --gc_record_bc_elim                     false
% 7.89/1.50  
% 7.89/1.50  ------ Preprocessing Options
% 7.89/1.50  
% 7.89/1.50  --preprocessing_flag                    true
% 7.89/1.50  --time_out_prep_mult                    0.1
% 7.89/1.50  --splitting_mode                        input
% 7.89/1.50  --splitting_grd                         true
% 7.89/1.50  --splitting_cvd                         false
% 7.89/1.50  --splitting_cvd_svl                     false
% 7.89/1.50  --splitting_nvd                         32
% 7.89/1.50  --sub_typing                            true
% 7.89/1.50  --prep_gs_sim                           true
% 7.89/1.50  --prep_unflatten                        true
% 7.89/1.50  --prep_res_sim                          true
% 7.89/1.50  --prep_upred                            true
% 7.89/1.50  --prep_sem_filter                       exhaustive
% 7.89/1.50  --prep_sem_filter_out                   false
% 7.89/1.50  --pred_elim                             true
% 7.89/1.50  --res_sim_input                         true
% 7.89/1.50  --eq_ax_congr_red                       true
% 7.89/1.50  --pure_diseq_elim                       true
% 7.89/1.50  --brand_transform                       false
% 7.89/1.50  --non_eq_to_eq                          false
% 7.89/1.50  --prep_def_merge                        true
% 7.89/1.50  --prep_def_merge_prop_impl              false
% 7.89/1.50  --prep_def_merge_mbd                    true
% 7.89/1.50  --prep_def_merge_tr_red                 false
% 7.89/1.50  --prep_def_merge_tr_cl                  false
% 7.89/1.50  --smt_preprocessing                     true
% 7.89/1.50  --smt_ac_axioms                         fast
% 7.89/1.50  --preprocessed_out                      false
% 7.89/1.50  --preprocessed_stats                    false
% 7.89/1.50  
% 7.89/1.50  ------ Abstraction refinement Options
% 7.89/1.50  
% 7.89/1.50  --abstr_ref                             []
% 7.89/1.50  --abstr_ref_prep                        false
% 7.89/1.50  --abstr_ref_until_sat                   false
% 7.89/1.50  --abstr_ref_sig_restrict                funpre
% 7.89/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.89/1.50  --abstr_ref_under                       []
% 7.89/1.50  
% 7.89/1.50  ------ SAT Options
% 7.89/1.50  
% 7.89/1.50  --sat_mode                              false
% 7.89/1.50  --sat_fm_restart_options                ""
% 7.89/1.50  --sat_gr_def                            false
% 7.89/1.50  --sat_epr_types                         true
% 7.89/1.50  --sat_non_cyclic_types                  false
% 7.89/1.50  --sat_finite_models                     false
% 7.89/1.50  --sat_fm_lemmas                         false
% 7.89/1.50  --sat_fm_prep                           false
% 7.89/1.50  --sat_fm_uc_incr                        true
% 7.89/1.50  --sat_out_model                         small
% 7.89/1.50  --sat_out_clauses                       false
% 7.89/1.50  
% 7.89/1.50  ------ QBF Options
% 7.89/1.50  
% 7.89/1.50  --qbf_mode                              false
% 7.89/1.50  --qbf_elim_univ                         false
% 7.89/1.50  --qbf_dom_inst                          none
% 7.89/1.50  --qbf_dom_pre_inst                      false
% 7.89/1.50  --qbf_sk_in                             false
% 7.89/1.50  --qbf_pred_elim                         true
% 7.89/1.50  --qbf_split                             512
% 7.89/1.50  
% 7.89/1.50  ------ BMC1 Options
% 7.89/1.50  
% 7.89/1.50  --bmc1_incremental                      false
% 7.89/1.50  --bmc1_axioms                           reachable_all
% 7.89/1.50  --bmc1_min_bound                        0
% 7.89/1.50  --bmc1_max_bound                        -1
% 7.89/1.50  --bmc1_max_bound_default                -1
% 7.89/1.50  --bmc1_symbol_reachability              true
% 7.89/1.50  --bmc1_property_lemmas                  false
% 7.89/1.51  --bmc1_k_induction                      false
% 7.89/1.51  --bmc1_non_equiv_states                 false
% 7.89/1.51  --bmc1_deadlock                         false
% 7.89/1.51  --bmc1_ucm                              false
% 7.89/1.51  --bmc1_add_unsat_core                   none
% 7.89/1.51  --bmc1_unsat_core_children              false
% 7.89/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.89/1.51  --bmc1_out_stat                         full
% 7.89/1.51  --bmc1_ground_init                      false
% 7.89/1.51  --bmc1_pre_inst_next_state              false
% 7.89/1.51  --bmc1_pre_inst_state                   false
% 7.89/1.51  --bmc1_pre_inst_reach_state             false
% 7.89/1.51  --bmc1_out_unsat_core                   false
% 7.89/1.51  --bmc1_aig_witness_out                  false
% 7.89/1.51  --bmc1_verbose                          false
% 7.89/1.51  --bmc1_dump_clauses_tptp                false
% 7.89/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.89/1.51  --bmc1_dump_file                        -
% 7.89/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.89/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.89/1.51  --bmc1_ucm_extend_mode                  1
% 7.89/1.51  --bmc1_ucm_init_mode                    2
% 7.89/1.51  --bmc1_ucm_cone_mode                    none
% 7.89/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.89/1.51  --bmc1_ucm_relax_model                  4
% 7.89/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.89/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.89/1.51  --bmc1_ucm_layered_model                none
% 7.89/1.51  --bmc1_ucm_max_lemma_size               10
% 7.89/1.51  
% 7.89/1.51  ------ AIG Options
% 7.89/1.51  
% 7.89/1.51  --aig_mode                              false
% 7.89/1.51  
% 7.89/1.51  ------ Instantiation Options
% 7.89/1.51  
% 7.89/1.51  --instantiation_flag                    true
% 7.89/1.51  --inst_sos_flag                         true
% 7.89/1.51  --inst_sos_phase                        true
% 7.89/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.89/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.89/1.51  --inst_lit_sel_side                     none
% 7.89/1.51  --inst_solver_per_active                1400
% 7.89/1.51  --inst_solver_calls_frac                1.
% 7.89/1.51  --inst_passive_queue_type               priority_queues
% 7.89/1.51  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 7.89/1.51  --inst_passive_queues_freq              [25;2]
% 7.89/1.51  --inst_dismatching                      true
% 7.89/1.51  --inst_eager_unprocessed_to_passive     true
% 7.89/1.51  --inst_prop_sim_given                   true
% 7.89/1.51  --inst_prop_sim_new                     false
% 7.89/1.51  --inst_subs_new                         false
% 7.89/1.51  --inst_eq_res_simp                      false
% 7.89/1.51  --inst_subs_given                       false
% 7.89/1.51  --inst_orphan_elimination               true
% 7.89/1.51  --inst_learning_loop_flag               true
% 7.89/1.51  --inst_learning_start                   3000
% 7.89/1.51  --inst_learning_factor                  2
% 7.89/1.51  --inst_start_prop_sim_after_learn       3
% 7.89/1.51  --inst_sel_renew                        solver
% 7.89/1.51  --inst_lit_activity_flag                true
% 7.89/1.51  --inst_restr_to_given                   false
% 7.89/1.51  --inst_activity_threshold               500
% 7.89/1.51  --inst_out_proof                        true
% 7.89/1.51  
% 7.89/1.51  ------ Resolution Options
% 7.89/1.51  
% 7.89/1.51  --resolution_flag                       false
% 7.89/1.51  --res_lit_sel                           adaptive
% 7.89/1.51  --res_lit_sel_side                      none
% 7.89/1.51  --res_ordering                          kbo
% 7.89/1.51  --res_to_prop_solver                    active
% 7.89/1.51  --res_prop_simpl_new                    false
% 7.89/1.51  --res_prop_simpl_given                  true
% 7.89/1.51  --res_passive_queue_type                priority_queues
% 7.89/1.51  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 7.89/1.51  --res_passive_queues_freq               [15;5]
% 7.89/1.51  --res_forward_subs                      full
% 7.89/1.51  --res_backward_subs                     full
% 7.89/1.51  --res_forward_subs_resolution           true
% 7.89/1.51  --res_backward_subs_resolution          true
% 7.89/1.51  --res_orphan_elimination                true
% 7.89/1.51  --res_time_limit                        2.
% 7.89/1.51  --res_out_proof                         true
% 7.89/1.51  
% 7.89/1.51  ------ Superposition Options
% 7.89/1.51  
% 7.89/1.51  --superposition_flag                    true
% 7.89/1.51  --sup_passive_queue_type                priority_queues
% 7.89/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.89/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.89/1.51  --demod_completeness_check              fast
% 7.89/1.51  --demod_use_ground                      true
% 7.89/1.51  --sup_to_prop_solver                    passive
% 7.89/1.51  --sup_prop_simpl_new                    true
% 7.89/1.51  --sup_prop_simpl_given                  true
% 7.89/1.51  --sup_fun_splitting                     true
% 7.89/1.51  --sup_smt_interval                      50000
% 7.89/1.51  
% 7.89/1.51  ------ Superposition Simplification Setup
% 7.89/1.51  
% 7.89/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.89/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.89/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.89/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.89/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.89/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.89/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.89/1.51  --sup_immed_triv                        [TrivRules]
% 7.89/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.51  --sup_immed_bw_main                     []
% 7.89/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.89/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.89/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.89/1.51  --sup_input_bw                          []
% 7.89/1.51  
% 7.89/1.51  ------ Combination Options
% 7.89/1.51  
% 7.89/1.51  --comb_res_mult                         3
% 7.89/1.51  --comb_sup_mult                         2
% 7.89/1.51  --comb_inst_mult                        10
% 7.89/1.51  
% 7.89/1.51  ------ Debug Options
% 7.89/1.51  
% 7.89/1.51  --dbg_backtrace                         false
% 7.89/1.51  --dbg_dump_prop_clauses                 false
% 7.89/1.51  --dbg_dump_prop_clauses_file            -
% 7.89/1.51  --dbg_out_stat                          false
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  ------ Proving...
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  % SZS status Theorem for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  fof(f5,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f16,plain,(
% 7.89/1.51    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f5])).
% 7.89/1.51  
% 7.89/1.51  fof(f31,plain,(
% 7.89/1.51    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(nnf_transformation,[],[f16])).
% 7.89/1.51  
% 7.89/1.51  fof(f32,plain,(
% 7.89/1.51    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(flattening,[],[f31])).
% 7.89/1.51  
% 7.89/1.51  fof(f33,plain,(
% 7.89/1.51    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(rectify,[],[f32])).
% 7.89/1.51  
% 7.89/1.51  fof(f34,plain,(
% 7.89/1.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f35,plain,(
% 7.89/1.51    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 7.89/1.51  
% 7.89/1.51  fof(f62,plain,(
% 7.89/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f35])).
% 7.89/1.51  
% 7.89/1.51  fof(f91,plain,(
% 7.89/1.51    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(equality_resolution,[],[f62])).
% 7.89/1.51  
% 7.89/1.51  fof(f10,conjecture,(
% 7.89/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f11,negated_conjecture,(
% 7.89/1.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 7.89/1.51    inference(negated_conjecture,[],[f10])).
% 7.89/1.51  
% 7.89/1.51  fof(f23,plain,(
% 7.89/1.51    ? [X0,X1,X2] : ((~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 7.89/1.51    inference(ennf_transformation,[],[f11])).
% 7.89/1.51  
% 7.89/1.51  fof(f24,plain,(
% 7.89/1.51    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.89/1.51    inference(flattening,[],[f23])).
% 7.89/1.51  
% 7.89/1.51  fof(f50,plain,(
% 7.89/1.51    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) & v2_wellord1(sK11) & v1_relat_1(sK11))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f51,plain,(
% 7.89/1.51    ~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) & v2_wellord1(sK11) & v1_relat_1(sK11)),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f24,f50])).
% 7.89/1.51  
% 7.89/1.51  fof(f87,plain,(
% 7.89/1.51    v1_relat_1(sK11)),
% 7.89/1.51    inference(cnf_transformation,[],[f51])).
% 7.89/1.51  
% 7.89/1.51  fof(f7,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f18,plain,(
% 7.89/1.51    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f7])).
% 7.89/1.51  
% 7.89/1.51  fof(f19,plain,(
% 7.89/1.51    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(flattening,[],[f18])).
% 7.89/1.51  
% 7.89/1.51  fof(f38,plain,(
% 7.89/1.51    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(nnf_transformation,[],[f19])).
% 7.89/1.51  
% 7.89/1.51  fof(f39,plain,(
% 7.89/1.51    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(rectify,[],[f38])).
% 7.89/1.51  
% 7.89/1.51  fof(f40,plain,(
% 7.89/1.51    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f41,plain,(
% 7.89/1.51    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f40])).
% 7.89/1.51  
% 7.89/1.51  fof(f73,plain,(
% 7.89/1.51    ( ! [X6,X4,X0,X5] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f41])).
% 7.89/1.51  
% 7.89/1.51  fof(f6,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f17,plain,(
% 7.89/1.51    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f6])).
% 7.89/1.51  
% 7.89/1.51  fof(f36,plain,(
% 7.89/1.51    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(nnf_transformation,[],[f17])).
% 7.89/1.51  
% 7.89/1.51  fof(f37,plain,(
% 7.89/1.51    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(flattening,[],[f36])).
% 7.89/1.51  
% 7.89/1.51  fof(f68,plain,(
% 7.89/1.51    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f37])).
% 7.89/1.51  
% 7.89/1.51  fof(f88,plain,(
% 7.89/1.51    v2_wellord1(sK11)),
% 7.89/1.51    inference(cnf_transformation,[],[f51])).
% 7.89/1.51  
% 7.89/1.51  fof(f63,plain,(
% 7.89/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f35])).
% 7.89/1.51  
% 7.89/1.51  fof(f90,plain,(
% 7.89/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(equality_resolution,[],[f63])).
% 7.89/1.51  
% 7.89/1.51  fof(f9,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f22,plain,(
% 7.89/1.51    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f9])).
% 7.89/1.51  
% 7.89/1.51  fof(f46,plain,(
% 7.89/1.51    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(nnf_transformation,[],[f22])).
% 7.89/1.51  
% 7.89/1.51  fof(f47,plain,(
% 7.89/1.51    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(rectify,[],[f46])).
% 7.89/1.51  
% 7.89/1.51  fof(f48,plain,(
% 7.89/1.51    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & ~r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) & sK7(X0) != sK8(X0) & r2_hidden(sK8(X0),k3_relat_1(X0)) & r2_hidden(sK7(X0),k3_relat_1(X0))))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f49,plain,(
% 7.89/1.51    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & ~r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) & sK7(X0) != sK8(X0) & r2_hidden(sK8(X0),k3_relat_1(X0)) & r2_hidden(sK7(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f48])).
% 7.89/1.51  
% 7.89/1.51  fof(f81,plain,(
% 7.89/1.51    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f49])).
% 7.89/1.51  
% 7.89/1.51  fof(f70,plain,(
% 7.89/1.51    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f37])).
% 7.89/1.51  
% 7.89/1.51  fof(f8,axiom,(
% 7.89/1.51    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f20,plain,(
% 7.89/1.51    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(ennf_transformation,[],[f8])).
% 7.89/1.51  
% 7.89/1.51  fof(f21,plain,(
% 7.89/1.51    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(flattening,[],[f20])).
% 7.89/1.51  
% 7.89/1.51  fof(f42,plain,(
% 7.89/1.51    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(nnf_transformation,[],[f21])).
% 7.89/1.51  
% 7.89/1.51  fof(f43,plain,(
% 7.89/1.51    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(rectify,[],[f42])).
% 7.89/1.51  
% 7.89/1.51  fof(f44,plain,(
% 7.89/1.51    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK5(X0) != sK6(X0) & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f45,plain,(
% 7.89/1.51    ! [X0] : (((v4_relat_2(X0) | (sK5(X0) != sK6(X0) & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f44])).
% 7.89/1.51  
% 7.89/1.51  fof(f77,plain,(
% 7.89/1.51    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f45])).
% 7.89/1.51  
% 7.89/1.51  fof(f69,plain,(
% 7.89/1.51    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f37])).
% 7.89/1.51  
% 7.89/1.51  fof(f4,axiom,(
% 7.89/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f14,plain,(
% 7.89/1.51    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 7.89/1.51    inference(ennf_transformation,[],[f4])).
% 7.89/1.51  
% 7.89/1.51  fof(f15,plain,(
% 7.89/1.51    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 7.89/1.51    inference(flattening,[],[f14])).
% 7.89/1.51  
% 7.89/1.51  fof(f60,plain,(
% 7.89/1.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f15])).
% 7.89/1.51  
% 7.89/1.51  fof(f1,axiom,(
% 7.89/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f13,plain,(
% 7.89/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.89/1.51    inference(ennf_transformation,[],[f1])).
% 7.89/1.51  
% 7.89/1.51  fof(f25,plain,(
% 7.89/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.51    inference(nnf_transformation,[],[f13])).
% 7.89/1.51  
% 7.89/1.51  fof(f26,plain,(
% 7.89/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.51    inference(rectify,[],[f25])).
% 7.89/1.51  
% 7.89/1.51  fof(f27,plain,(
% 7.89/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.89/1.51    introduced(choice_axiom,[])).
% 7.89/1.51  
% 7.89/1.51  fof(f28,plain,(
% 7.89/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.89/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.89/1.51  
% 7.89/1.51  fof(f54,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f2,axiom,(
% 7.89/1.51    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f29,plain,(
% 7.89/1.51    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 7.89/1.51    inference(nnf_transformation,[],[f2])).
% 7.89/1.51  
% 7.89/1.51  fof(f30,plain,(
% 7.89/1.51    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 7.89/1.51    inference(flattening,[],[f29])).
% 7.89/1.51  
% 7.89/1.51  fof(f57,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f30])).
% 7.89/1.51  
% 7.89/1.51  fof(f89,plain,(
% 7.89/1.51    ~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))),
% 7.89/1.51    inference(cnf_transformation,[],[f51])).
% 7.89/1.51  
% 7.89/1.51  fof(f53,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f28])).
% 7.89/1.51  
% 7.89/1.51  fof(f56,plain,(
% 7.89/1.51    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f30])).
% 7.89/1.51  
% 7.89/1.51  fof(f3,axiom,(
% 7.89/1.51    ! [X0,X1] : r3_xboole_0(X0,X0)),
% 7.89/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.51  
% 7.89/1.51  fof(f12,plain,(
% 7.89/1.51    ! [X0] : r3_xboole_0(X0,X0)),
% 7.89/1.51    inference(rectify,[],[f3])).
% 7.89/1.51  
% 7.89/1.51  fof(f58,plain,(
% 7.89/1.51    ( ! [X0] : (r3_xboole_0(X0,X0)) )),
% 7.89/1.51    inference(cnf_transformation,[],[f12])).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1371,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.89/1.51      theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2248,plain,
% 7.89/1.51      ( r2_hidden(X0,X1)
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
% 7.89/1.51      | X1 != k1_wellord1(sK11,sK10)
% 7.89/1.51      | X0 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1371]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4738,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(sK11,sK10))
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
% 7.89/1.51      | X0 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
% 7.89/1.51      | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2248]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_21191,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
% 7.89/1.51      | r2_hidden(sK9,k1_wellord1(sK11,sK10))
% 7.89/1.51      | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10)
% 7.89/1.51      | sK9 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_4738]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2243,plain,
% 7.89/1.51      ( r2_hidden(X0,X1)
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 7.89/1.51      | X1 != k1_wellord1(sK11,sK9)
% 7.89/1.51      | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1371]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4722,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 7.89/1.51      | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 7.89/1.51      | k1_wellord1(X1,X2) != k1_wellord1(sK11,sK9) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2243]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7628,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 7.89/1.51      | r2_hidden(sK10,k1_wellord1(X0,X1))
% 7.89/1.51      | k1_wellord1(X0,X1) != k1_wellord1(sK11,sK9)
% 7.89/1.51      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_4722]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_18394,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 7.89/1.51      | r2_hidden(sK10,k1_wellord1(sK11,sK9))
% 7.89/1.51      | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
% 7.89/1.51      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_7628]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_13,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | ~ v1_relat_1(X1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_37,negated_conjecture,
% 7.89/1.51      ( v1_relat_1(sK11) ),
% 7.89/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_990,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | sK11 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_991,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_990]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_5795,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK9,X0),sK11)
% 7.89/1.51      | ~ r2_hidden(sK9,k1_wellord1(sK11,X0)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_991]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_12729,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK9,sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(sK9,k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_5795]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_24,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 7.89/1.51      | r2_hidden(k4_tarski(X3,X1),X2)
% 7.89/1.51      | ~ v8_relat_2(X2)
% 7.89/1.51      | ~ v1_relat_1(X2) ),
% 7.89/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1122,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 7.89/1.51      | r2_hidden(k4_tarski(X3,X1),X2)
% 7.89/1.51      | ~ v8_relat_2(X2)
% 7.89/1.51      | sK11 != X2 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1123,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X1),sK11)
% 7.89/1.51      | ~ v8_relat_2(sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_1122]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_19,plain,
% 7.89/1.51      ( v8_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_36,negated_conjecture,
% 7.89/1.51      ( v2_wellord1(sK11) ),
% 7.89/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_415,plain,
% 7.89/1.51      ( v8_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_416,plain,
% 7.89/1.51      ( v8_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_415]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_85,plain,
% 7.89/1.51      ( v8_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_418,plain,
% 7.89/1.51      ( v8_relat_2(sK11) ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_416,c_37,c_36,c_85]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_720,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 7.89/1.51      | r2_hidden(k4_tarski(X3,X1),X2)
% 7.89/1.51      | ~ v1_relat_1(X2)
% 7.89/1.51      | sK11 != X2 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_418]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_721,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X1),sK11)
% 7.89/1.51      | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_720]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_723,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(X2,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_721,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_724,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X1),sK11) ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_723]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1125,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(X2,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_1123,c_37,c_721]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1126,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X1),sK11) ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_1125]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3306,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(X0,sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1126]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_12152,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK9,sK10),sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_3306]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_12,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | ~ v1_relat_1(X1)
% 7.89/1.51      | X0 = X2 ),
% 7.89/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1000,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | X2 = X0
% 7.89/1.51      | sK11 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1001,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(sK11,X1))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | X1 = X0 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_1000]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3902,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(sK11,sK9))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,sK9),sK11)
% 7.89/1.51      | sK9 = X0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1001]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_10493,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK9),sK11)
% 7.89/1.51      | r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK9))
% 7.89/1.51      | sK9 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_3902]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2063,plain,
% 7.89/1.51      ( r2_hidden(X0,k1_wellord1(sK11,sK10))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,sK10),sK11)
% 7.89/1.51      | sK10 = X0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1001]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6372,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
% 7.89/1.51      | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
% 7.89/1.51      | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2063]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2486,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK10,sK9),sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1126]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6203,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK10,sK9),sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2486]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_34,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.89/1.51      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.89/1.51      | ~ v6_relat_2(X1)
% 7.89/1.51      | ~ v1_relat_1(X1)
% 7.89/1.51      | X0 = X2 ),
% 7.89/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_957,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.89/1.51      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | ~ v6_relat_2(X1)
% 7.89/1.51      | X2 = X0
% 7.89/1.51      | sK11 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_34,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_958,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | ~ v6_relat_2(sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_957]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_17,plain,
% 7.89/1.51      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_437,plain,
% 7.89/1.51      ( v6_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_438,plain,
% 7.89/1.51      ( v6_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_437]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_91,plain,
% 7.89/1.51      ( v6_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_17]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_440,plain,
% 7.89/1.51      ( v6_relat_2(sK11) ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_438,c_37,c_36,c_91]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_890,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.89/1.51      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.89/1.51      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.89/1.51      | ~ v1_relat_1(X1)
% 7.89/1.51      | X2 = X0
% 7.89/1.51      | sK11 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_34,c_440]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_891,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | ~ v1_relat_1(sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_890]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_895,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_891,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_896,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_895]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_961,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_958,c_37,c_891]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_962,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 7.89/1.51      | r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_961]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2057,plain,
% 7.89/1.51      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | r2_hidden(k4_tarski(X0,sK10),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(sK10,X0),sK11)
% 7.89/1.51      | ~ r2_hidden(sK10,k3_relat_1(sK11))
% 7.89/1.51      | sK10 = X0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_962]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4574,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK10,sK9),sK11)
% 7.89/1.51      | r2_hidden(k4_tarski(sK9,sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(sK10,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(sK9,k3_relat_1(sK11))
% 7.89/1.51      | sK10 = sK9 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2057]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1374,plain,
% 7.89/1.51      ( X0 != X1 | X2 != X3 | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
% 7.89/1.51      theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3059,plain,
% 7.89/1.51      ( X0 != sK9
% 7.89/1.51      | k1_wellord1(sK11,X0) = k1_wellord1(sK11,sK9)
% 7.89/1.51      | sK11 != sK11 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1374]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4126,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK9)
% 7.89/1.51      | sK10 != sK9
% 7.89/1.51      | sK11 != sK11 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_3059]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_28,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 7.89/1.51      | ~ v4_relat_2(X2)
% 7.89/1.51      | ~ v1_relat_1(X2)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1105,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 7.89/1.51      | ~ v4_relat_2(X2)
% 7.89/1.51      | X1 = X0
% 7.89/1.51      | sK11 != X2 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1106,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | ~ v4_relat_2(sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_1105]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_18,plain,
% 7.89/1.51      ( v4_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_426,plain,
% 7.89/1.51      ( v4_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_427,plain,
% 7.89/1.51      ( v4_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_426]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_88,plain,
% 7.89/1.51      ( v4_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_429,plain,
% 7.89/1.51      ( v4_relat_2(sK11) ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_427,c_37,c_36,c_88]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_624,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 7.89/1.51      | ~ v1_relat_1(X2)
% 7.89/1.51      | X1 = X0
% 7.89/1.51      | sK11 != X2 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_429]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_625,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | ~ v1_relat_1(sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_624]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1108,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | X0 = X1 ),
% 7.89/1.51      inference(global_propositional_subsumption,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_1106,c_37,c_625]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1109,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 7.89/1.51      | X1 = X0 ),
% 7.89/1.51      inference(renaming,[status(thm)],[c_1108]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2062,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK10,X0),sK11)
% 7.89/1.51      | sK10 = X0 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1109]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3315,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
% 7.89/1.51      | sK10 = sK9 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_2062]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1368,plain,( X0 = X0 ),theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2905,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK9) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1368]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1369,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1721,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) != X0
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X0
% 7.89/1.51      | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1369]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1805,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) != k1_wellord1(X0,X1)
% 7.89/1.51      | k1_wellord1(sK11,sK9) != k1_wellord1(X0,X1)
% 7.89/1.51      | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1721]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2702,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK9)
% 7.89/1.51      | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10)
% 7.89/1.51      | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1805]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2520,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK10,sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_991]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_2080,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK10) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1368]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_7,plain,
% 7.89/1.51      ( r2_hidden(X0,k3_relat_1(X1))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.89/1.51      | ~ v1_relat_1(X1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1025,plain,
% 7.89/1.51      ( r2_hidden(X0,k3_relat_1(X1))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.89/1.51      | sK11 != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_37]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1026,plain,
% 7.89/1.51      ( r2_hidden(X0,k3_relat_1(sK11))
% 7.89/1.51      | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_1025]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1996,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 7.89/1.51      | r2_hidden(sK10,k3_relat_1(sK11)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1964,plain,
% 7.89/1.51      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
% 7.89/1.51      | r2_hidden(sK9,k3_relat_1(sK11)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1026]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1778,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_991]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1773,plain,
% 7.89/1.51      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
% 7.89/1.51      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_991]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1383,plain,
% 7.89/1.51      ( sK11 = sK11 ),
% 7.89/1.51      inference(instantiation,[status(thm)],[c_1368]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_0,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_3,plain,
% 7.89/1.51      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_35,negated_conjecture,
% 7.89/1.51      ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_472,plain,
% 7.89/1.51      ( ~ r1_tarski(X0,X1)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X0
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_3,c_35]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_473,plain,
% 7.89/1.51      ( ~ r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_472]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_538,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X0
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_473]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_539,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_538]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_1,plain,
% 7.89/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_531,plain,
% 7.89/1.51      ( r2_hidden(sK0(X0,X1),X0)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X0
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X1 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_473]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_532,plain,
% 7.89/1.51      ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_531]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_4,plain,
% 7.89/1.51      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) ),
% 7.89/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_465,plain,
% 7.89/1.51      ( ~ r1_tarski(X0,X1)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X1
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_4,c_35]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_466,plain,
% 7.89/1.51      ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_465]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_524,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X1
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_466]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_525,plain,
% 7.89/1.51      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_524]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_517,plain,
% 7.89/1.51      ( r2_hidden(sK0(X0,X1),X0)
% 7.89/1.51      | k1_wellord1(sK11,sK10) != X1
% 7.89/1.51      | k1_wellord1(sK11,sK9) != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_466]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_518,plain,
% 7.89/1.51      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_517]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_6,plain,
% 7.89/1.51      ( r3_xboole_0(X0,X0) ),
% 7.89/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_479,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK10) != X0 | k1_wellord1(sK11,sK9) != X0 ),
% 7.89/1.51      inference(resolution_lifted,[status(thm)],[c_6,c_35]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(c_480,plain,
% 7.89/1.51      ( k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK10) ),
% 7.89/1.51      inference(unflattening,[status(thm)],[c_479]) ).
% 7.89/1.51  
% 7.89/1.51  cnf(contradiction,plain,
% 7.89/1.51      ( $false ),
% 7.89/1.51      inference(minisat,
% 7.89/1.51                [status(thm)],
% 7.89/1.51                [c_21191,c_18394,c_12729,c_12152,c_10493,c_6372,c_6203,
% 7.89/1.51                 c_4574,c_4126,c_3315,c_2905,c_2702,c_2520,c_2080,c_1996,
% 7.89/1.51                 c_1964,c_1778,c_1773,c_1383,c_539,c_532,c_525,c_518,
% 7.89/1.51                 c_480]) ).
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.51  
% 7.89/1.51  ------                               Statistics
% 7.89/1.51  
% 7.89/1.51  ------ General
% 7.89/1.51  
% 7.89/1.51  abstr_ref_over_cycles:                  0
% 7.89/1.51  abstr_ref_under_cycles:                 0
% 7.89/1.51  gc_basic_clause_elim:                   0
% 7.89/1.51  forced_gc_time:                         0
% 7.89/1.51  parsing_time:                           0.008
% 7.89/1.51  unif_index_cands_time:                  0.
% 7.89/1.51  unif_index_add_time:                    0.
% 7.89/1.51  orderings_time:                         0.
% 7.89/1.51  out_proof_time:                         0.011
% 7.89/1.51  total_time:                             0.798
% 7.89/1.51  num_of_symbols:                         56
% 7.89/1.51  num_of_terms:                           18164
% 7.89/1.51  
% 7.89/1.51  ------ Preprocessing
% 7.89/1.51  
% 7.89/1.51  num_of_splits:                          0
% 7.89/1.51  num_of_split_atoms:                     0
% 7.89/1.51  num_of_reused_defs:                     0
% 7.89/1.51  num_eq_ax_congr_red:                    30
% 7.89/1.51  num_of_sem_filtered_clauses:            1
% 7.89/1.51  num_of_subtypes:                        0
% 7.89/1.51  monotx_restored_types:                  0
% 7.89/1.51  sat_num_of_epr_types:                   0
% 7.89/1.51  sat_num_of_non_cyclic_types:            0
% 7.89/1.51  sat_guarded_non_collapsed_types:        0
% 7.89/1.51  num_pure_diseq_elim:                    0
% 7.89/1.51  simp_replaced_by:                       0
% 7.89/1.51  res_preprocessed:                       109
% 7.89/1.51  prep_upred:                             0
% 7.89/1.51  prep_unflattend:                        78
% 7.89/1.51  smt_new_axioms:                         0
% 7.89/1.51  pred_elim_cands:                        2
% 7.89/1.51  pred_elim:                              8
% 7.89/1.51  pred_elim_cl:                           20
% 7.89/1.51  pred_elim_cycles:                       14
% 7.89/1.51  merged_defs:                            0
% 7.89/1.51  merged_defs_ncl:                        0
% 7.89/1.51  bin_hyper_res:                          0
% 7.89/1.51  prep_cycles:                            4
% 7.89/1.51  pred_elim_time:                         0.009
% 7.89/1.51  splitting_time:                         0.
% 7.89/1.51  sem_filter_time:                        0.
% 7.89/1.51  monotx_time:                            0.
% 7.89/1.51  subtype_inf_time:                       0.
% 7.89/1.51  
% 7.89/1.51  ------ Problem properties
% 7.89/1.51  
% 7.89/1.51  clauses:                                18
% 7.89/1.51  conjectures:                            0
% 7.89/1.51  epr:                                    2
% 7.89/1.51  horn:                                   12
% 7.89/1.51  ground:                                 3
% 7.89/1.51  unary:                                  5
% 7.89/1.51  binary:                                 5
% 7.89/1.51  lits:                                   42
% 7.89/1.51  lits_eq:                                9
% 7.89/1.51  fd_pure:                                0
% 7.89/1.51  fd_pseudo:                              0
% 7.89/1.51  fd_cond:                                0
% 7.89/1.51  fd_pseudo_cond:                         5
% 7.89/1.51  ac_symbols:                             0
% 7.89/1.51  
% 7.89/1.51  ------ Propositional Solver
% 7.89/1.51  
% 7.89/1.51  prop_solver_calls:                      30
% 7.89/1.51  prop_fast_solver_calls:                 1676
% 7.89/1.51  smt_solver_calls:                       0
% 7.89/1.51  smt_fast_solver_calls:                  0
% 7.89/1.51  prop_num_of_clauses:                    8744
% 7.89/1.51  prop_preprocess_simplified:             19293
% 7.89/1.51  prop_fo_subsumed:                       22
% 7.89/1.51  prop_solver_time:                       0.
% 7.89/1.51  smt_solver_time:                        0.
% 7.89/1.51  smt_fast_solver_time:                   0.
% 7.89/1.51  prop_fast_solver_time:                  0.
% 7.89/1.51  prop_unsat_core_time:                   0.001
% 7.89/1.51  
% 7.89/1.51  ------ QBF
% 7.89/1.51  
% 7.89/1.51  qbf_q_res:                              0
% 7.89/1.51  qbf_num_tautologies:                    0
% 7.89/1.51  qbf_prep_cycles:                        0
% 7.89/1.51  
% 7.89/1.51  ------ BMC1
% 7.89/1.51  
% 7.89/1.51  bmc1_current_bound:                     -1
% 7.89/1.51  bmc1_last_solved_bound:                 -1
% 7.89/1.51  bmc1_unsat_core_size:                   -1
% 7.89/1.51  bmc1_unsat_core_parents_size:           -1
% 7.89/1.51  bmc1_merge_next_fun:                    0
% 7.89/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.89/1.51  
% 7.89/1.51  ------ Instantiation
% 7.89/1.51  
% 7.89/1.51  inst_num_of_clauses:                    2208
% 7.89/1.51  inst_num_in_passive:                    1226
% 7.89/1.51  inst_num_in_active:                     849
% 7.89/1.51  inst_num_in_unprocessed:                135
% 7.89/1.51  inst_num_of_loops:                      1177
% 7.89/1.51  inst_num_of_learning_restarts:          0
% 7.89/1.51  inst_num_moves_active_passive:          327
% 7.89/1.51  inst_lit_activity:                      0
% 7.89/1.51  inst_lit_activity_moves:                1
% 7.89/1.51  inst_num_tautologies:                   0
% 7.89/1.51  inst_num_prop_implied:                  0
% 7.89/1.51  inst_num_existing_simplified:           0
% 7.89/1.51  inst_num_eq_res_simplified:             0
% 7.89/1.51  inst_num_child_elim:                    0
% 7.89/1.51  inst_num_of_dismatching_blockings:      1264
% 7.89/1.51  inst_num_of_non_proper_insts:           2683
% 7.89/1.51  inst_num_of_duplicates:                 0
% 7.89/1.51  inst_inst_num_from_inst_to_res:         0
% 7.89/1.51  inst_dismatching_checking_time:         0.
% 7.89/1.51  
% 7.89/1.51  ------ Resolution
% 7.89/1.51  
% 7.89/1.51  res_num_of_clauses:                     0
% 7.89/1.51  res_num_in_passive:                     0
% 7.89/1.51  res_num_in_active:                      0
% 7.89/1.51  res_num_of_loops:                       113
% 7.89/1.51  res_forward_subset_subsumed:            338
% 7.89/1.51  res_backward_subset_subsumed:           6
% 7.89/1.51  res_forward_subsumed:                   0
% 7.89/1.51  res_backward_subsumed:                  0
% 7.89/1.51  res_forward_subsumption_resolution:     0
% 7.89/1.51  res_backward_subsumption_resolution:    0
% 7.89/1.51  res_clause_to_clause_subsumption:       11463
% 7.89/1.51  res_orphan_elimination:                 0
% 7.89/1.51  res_tautology_del:                      290
% 7.89/1.51  res_num_eq_res_simplified:              0
% 7.89/1.51  res_num_sel_changes:                    0
% 7.89/1.51  res_moves_from_active_to_pass:          0
% 7.89/1.51  
% 7.89/1.51  ------ Superposition
% 7.89/1.51  
% 7.89/1.51  sup_time_total:                         0.
% 7.89/1.51  sup_time_generating:                    0.
% 7.89/1.51  sup_time_sim_full:                      0.
% 7.89/1.51  sup_time_sim_immed:                     0.
% 7.89/1.51  
% 7.89/1.51  sup_num_of_clauses:                     976
% 7.89/1.51  sup_num_in_active:                      227
% 7.89/1.51  sup_num_in_passive:                     749
% 7.89/1.51  sup_num_of_loops:                       234
% 7.89/1.51  sup_fw_superposition:                   957
% 7.89/1.51  sup_bw_superposition:                   1357
% 7.89/1.51  sup_immediate_simplified:               849
% 7.89/1.51  sup_given_eliminated:                   1
% 7.89/1.51  comparisons_done:                       0
% 7.89/1.51  comparisons_avoided:                    6
% 7.89/1.51  
% 7.89/1.51  ------ Simplifications
% 7.89/1.51  
% 7.89/1.51  
% 7.89/1.51  sim_fw_subset_subsumed:                 310
% 7.89/1.51  sim_bw_subset_subsumed:                 85
% 7.89/1.51  sim_fw_subsumed:                        452
% 7.89/1.51  sim_bw_subsumed:                        23
% 7.89/1.51  sim_fw_subsumption_res:                 0
% 7.89/1.51  sim_bw_subsumption_res:                 0
% 7.89/1.51  sim_tautology_del:                      48
% 7.89/1.51  sim_eq_tautology_del:                   46
% 7.89/1.51  sim_eq_res_simp:                        10
% 7.89/1.51  sim_fw_demodulated:                     0
% 7.89/1.51  sim_bw_demodulated:                     0
% 7.89/1.51  sim_light_normalised:                   0
% 7.89/1.51  sim_joinable_taut:                      0
% 7.89/1.51  sim_joinable_simp:                      0
% 7.89/1.51  sim_ac_normalised:                      0
% 7.89/1.51  sim_smt_subsumption:                    0
% 7.89/1.51  
%------------------------------------------------------------------------------
