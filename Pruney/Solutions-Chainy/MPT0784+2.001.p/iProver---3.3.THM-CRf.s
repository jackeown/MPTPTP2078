%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:30 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  233 (1337 expanded)
%              Number of clauses        :  156 ( 397 expanded)
%              Number of leaves         :   21 ( 259 expanded)
%              Depth                    :   22
%              Number of atoms          :  896 (6024 expanded)
%              Number of equality atoms :  270 ( 940 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f23,plain,(
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

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f48,f49])).

fof(f83,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
      & v2_wellord1(sK11)
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    & v2_wellord1(sK11)
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f25,f51])).

fof(f89,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f18])).

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

fof(f72,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f17])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f41])).

fof(f75,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f52])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK5(X0) != sK6(X0)
        & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
        & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f45])).

fof(f79,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f97,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_871,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_38])).

cnf(c_872,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v6_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_18,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,negated_conjecture,
    ( v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_458,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_459,plain,
    ( v6_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_92,plain,
    ( v6_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_461,plain,
    ( v6_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_38,c_37,c_92])).

cnf(c_804,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_461])).

cnf(c_805,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_38])).

cnf(c_810,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_809])).

cnf(c_875,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_38,c_805])).

cnf(c_876,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_875])).

cnf(c_1530,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1538,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_904,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_38])).

cnf(c_905,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_1528,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_2195,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X0),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_1528])).

cnf(c_25,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1036,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_1037,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v8_relat_2(sK11) ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_20,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_436,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_37])).

cnf(c_437,plain,
    ( v8_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_86,plain,
    ( v8_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_439,plain,
    ( v8_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_38,c_37,c_86])).

cnf(c_634,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_439])).

cnf(c_635,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_637,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_38])).

cnf(c_638,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_1039,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1037,c_38,c_635])).

cnf(c_1040,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_1039])).

cnf(c_1531,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top
    | r2_hidden(k4_tarski(X2,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_2633,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
    | r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,X1),X2)),sK11) != iProver_top
    | r1_tarski(k1_wellord1(sK11,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1531])).

cnf(c_3938,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) != iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_2633])).

cnf(c_9,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_927,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_38])).

cnf(c_928,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_1526,plain,
    ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_2635,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1526])).

cnf(c_19473,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | sK0(k1_wellord1(sK11,X0),X1) = X2
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3938,c_2635])).

cnf(c_19474,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_19473])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_914,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_38])).

cnf(c_915,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_1527,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_19483,plain,
    ( sK0(k1_wellord1(sK11,X0),X1) = X2
    | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k1_wellord1(sK11,X2)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_19474,c_1527])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1539,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_48301,plain,
    ( sK0(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = X1
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top
    | r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19483,c_1539])).

cnf(c_6,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,negated_conjecture,
    ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_424,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_36])).

cnf(c_425,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1533,plain,
    ( r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_48985,plain,
    ( sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) = sK9
    | r2_hidden(k4_tarski(sK9,sK10),sK11) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_48301,c_1533])).

cnf(c_7,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_36])).

cnf(c_418,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1534,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_48984,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_48301,c_1534])).

cnf(c_1221,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5352,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(sK11,X2))
    | X2 != X0
    | k1_wellord1(sK11,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_12985,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(X1,k1_wellord1(sK11,X1))
    | X1 != X0
    | k1_wellord1(sK11,X1) != k1_wellord1(sK11,X1) ),
    inference(instantiation,[status(thm)],[c_5352])).

cnf(c_43391,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | r2_hidden(sK10,k1_wellord1(sK11,sK10))
    | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10)
    | sK10 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_12985])).

cnf(c_1224,plain,
    ( X0 != X1
    | X2 != X3
    | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
    theory(equality)).

cnf(c_2024,plain,
    ( X0 != sK9
    | X1 != sK11
    | k1_wellord1(X1,X0) = k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_43074,plain,
    ( X0 != sK11
    | k1_wellord1(X0,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) = k1_wellord1(sK11,sK9)
    | sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_43080,plain,
    ( k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) = k1_wellord1(sK11,sK9)
    | sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != sK9
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_43074])).

cnf(c_1219,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2101,plain,
    ( X0 != X1
    | sK10 != X1
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_4906,plain,
    ( X0 != sK10
    | sK10 = X0
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_35903,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK10
    | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_4906])).

cnf(c_1697,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | X1 != k1_wellord1(sK11,sK9)
    | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_6887,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r2_hidden(sK10,X0)
    | X0 != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_33651,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_6887])).

cnf(c_33656,plain,
    ( k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33651])).

cnf(c_22863,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))))
    | k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_6887])).

cnf(c_22864,plain,
    ( k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
    | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22863])).

cnf(c_2740,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),X0)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | X0 != k1_wellord1(sK11,sK9)
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_4065,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,X0))
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,X0) != k1_wellord1(sK11,sK9)
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_13902,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))))
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
    | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_4065])).

cnf(c_3553,plain,
    ( r2_hidden(k4_tarski(sK10,X0),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_7970,plain,
    ( r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) ),
    inference(instantiation,[status(thm)],[c_3553])).

cnf(c_7972,plain,
    ( r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7970])).

cnf(c_29,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1019,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_1020,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v4_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_19,plain,
    ( v4_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_447,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_37])).

cnf(c_448,plain,
    ( v4_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_89,plain,
    ( v4_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_450,plain,
    ( v4_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_38,c_37,c_89])).

cnf(c_538,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_450])).

cnf(c_539,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1022,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_38,c_539])).

cnf(c_1023,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1022])).

cnf(c_2966,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,X0),sK11)
    | X0 = sK9 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_7965,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | sK10 = sK9 ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_7968,plain,
    ( sK10 = sK9
    | r2_hidden(k4_tarski(sK10,sK9),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7965])).

cnf(c_7964,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_3553])).

cnf(c_7966,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7964])).

cnf(c_2085,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_7553,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
    | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
    | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_1825,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | r2_hidden(k4_tarski(X0,sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_7547,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2296,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),X0),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_7546,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_6916,plain,
    ( X0 != sK11
    | k1_wellord1(X0,sK10) = k1_wellord1(sK11,sK9)
    | sK10 != sK9 ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_6924,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK9)
    | sK10 != sK9
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_6916])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_895,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_38])).

cnf(c_896,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X0)) ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_3547,plain,
    ( ~ r2_hidden(sK10,k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3227,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1218,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2741,plain,
    ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_2084,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK10,X0),sK11)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_2678,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | sK10 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_2679,plain,
    ( sK10 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
    | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2678])).

cnf(c_1220,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1687,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_1958,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK9),X0)
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2530,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
    | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK9)
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2100,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1959,plain,
    ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_8,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_939,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_38])).

cnf(c_940,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_1822,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | r2_hidden(sK10,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_1823,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) != iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_1798,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
    | r2_hidden(sK9,k3_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_1799,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_1750,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1726,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1727,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_1707,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
    | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1708,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_1679,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1680,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_1676,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1677,plain,
    ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) = iProver_top
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1676])).

cnf(c_1666,plain,
    ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
    | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_426,plain,
    ( r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_419,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_129,plain,
    ( ~ r1_tarski(sK11,sK11)
    | sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_125,plain,
    ( r1_tarski(sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48985,c_48984,c_43391,c_43080,c_35903,c_33656,c_22864,c_13902,c_7972,c_7968,c_7966,c_7553,c_7547,c_7546,c_6924,c_3547,c_3227,c_2741,c_2679,c_2530,c_2100,c_1959,c_1823,c_1799,c_1750,c_1727,c_1726,c_1708,c_1680,c_1679,c_1677,c_1676,c_1666,c_426,c_425,c_419,c_418,c_129,c_125])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.74/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/2.00  
% 11.74/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.74/2.00  
% 11.74/2.00  ------  iProver source info
% 11.74/2.00  
% 11.74/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.74/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.74/2.00  git: non_committed_changes: false
% 11.74/2.00  git: last_make_outside_of_git: false
% 11.74/2.00  
% 11.74/2.00  ------ 
% 11.74/2.00  
% 11.74/2.00  ------ Input Options
% 11.74/2.00  
% 11.74/2.00  --out_options                           all
% 11.74/2.00  --tptp_safe_out                         true
% 11.74/2.00  --problem_path                          ""
% 11.74/2.00  --include_path                          ""
% 11.74/2.00  --clausifier                            res/vclausify_rel
% 11.74/2.00  --clausifier_options                    --mode clausify
% 11.74/2.00  --stdin                                 false
% 11.74/2.00  --stats_out                             all
% 11.74/2.00  
% 11.74/2.00  ------ General Options
% 11.74/2.00  
% 11.74/2.00  --fof                                   false
% 11.74/2.00  --time_out_real                         305.
% 11.74/2.00  --time_out_virtual                      -1.
% 11.74/2.00  --symbol_type_check                     false
% 11.74/2.00  --clausify_out                          false
% 11.74/2.00  --sig_cnt_out                           false
% 11.74/2.00  --trig_cnt_out                          false
% 11.74/2.00  --trig_cnt_out_tolerance                1.
% 11.74/2.00  --trig_cnt_out_sk_spl                   false
% 11.74/2.00  --abstr_cl_out                          false
% 11.74/2.00  
% 11.74/2.00  ------ Global Options
% 11.74/2.00  
% 11.74/2.00  --schedule                              default
% 11.74/2.00  --add_important_lit                     false
% 11.74/2.00  --prop_solver_per_cl                    1000
% 11.74/2.00  --min_unsat_core                        false
% 11.74/2.00  --soft_assumptions                      false
% 11.74/2.00  --soft_lemma_size                       3
% 11.74/2.00  --prop_impl_unit_size                   0
% 11.74/2.00  --prop_impl_unit                        []
% 11.74/2.00  --share_sel_clauses                     true
% 11.74/2.00  --reset_solvers                         false
% 11.74/2.00  --bc_imp_inh                            [conj_cone]
% 11.74/2.00  --conj_cone_tolerance                   3.
% 11.74/2.00  --extra_neg_conj                        none
% 11.74/2.00  --large_theory_mode                     true
% 11.74/2.00  --prolific_symb_bound                   200
% 11.74/2.00  --lt_threshold                          2000
% 11.74/2.00  --clause_weak_htbl                      true
% 11.74/2.00  --gc_record_bc_elim                     false
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing Options
% 11.74/2.00  
% 11.74/2.00  --preprocessing_flag                    true
% 11.74/2.00  --time_out_prep_mult                    0.1
% 11.74/2.00  --splitting_mode                        input
% 11.74/2.00  --splitting_grd                         true
% 11.74/2.00  --splitting_cvd                         false
% 11.74/2.00  --splitting_cvd_svl                     false
% 11.74/2.00  --splitting_nvd                         32
% 11.74/2.00  --sub_typing                            true
% 11.74/2.00  --prep_gs_sim                           true
% 11.74/2.00  --prep_unflatten                        true
% 11.74/2.00  --prep_res_sim                          true
% 11.74/2.00  --prep_upred                            true
% 11.74/2.00  --prep_sem_filter                       exhaustive
% 11.74/2.00  --prep_sem_filter_out                   false
% 11.74/2.00  --pred_elim                             true
% 11.74/2.00  --res_sim_input                         true
% 11.74/2.00  --eq_ax_congr_red                       true
% 11.74/2.00  --pure_diseq_elim                       true
% 11.74/2.00  --brand_transform                       false
% 11.74/2.00  --non_eq_to_eq                          false
% 11.74/2.00  --prep_def_merge                        true
% 11.74/2.00  --prep_def_merge_prop_impl              false
% 11.74/2.00  --prep_def_merge_mbd                    true
% 11.74/2.00  --prep_def_merge_tr_red                 false
% 11.74/2.00  --prep_def_merge_tr_cl                  false
% 11.74/2.00  --smt_preprocessing                     true
% 11.74/2.00  --smt_ac_axioms                         fast
% 11.74/2.00  --preprocessed_out                      false
% 11.74/2.00  --preprocessed_stats                    false
% 11.74/2.00  
% 11.74/2.00  ------ Abstraction refinement Options
% 11.74/2.00  
% 11.74/2.00  --abstr_ref                             []
% 11.74/2.00  --abstr_ref_prep                        false
% 11.74/2.00  --abstr_ref_until_sat                   false
% 11.74/2.00  --abstr_ref_sig_restrict                funpre
% 11.74/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/2.00  --abstr_ref_under                       []
% 11.74/2.00  
% 11.74/2.00  ------ SAT Options
% 11.74/2.00  
% 11.74/2.00  --sat_mode                              false
% 11.74/2.00  --sat_fm_restart_options                ""
% 11.74/2.00  --sat_gr_def                            false
% 11.74/2.00  --sat_epr_types                         true
% 11.74/2.00  --sat_non_cyclic_types                  false
% 11.74/2.00  --sat_finite_models                     false
% 11.74/2.00  --sat_fm_lemmas                         false
% 11.74/2.00  --sat_fm_prep                           false
% 11.74/2.00  --sat_fm_uc_incr                        true
% 11.74/2.00  --sat_out_model                         small
% 11.74/2.00  --sat_out_clauses                       false
% 11.74/2.00  
% 11.74/2.00  ------ QBF Options
% 11.74/2.00  
% 11.74/2.00  --qbf_mode                              false
% 11.74/2.00  --qbf_elim_univ                         false
% 11.74/2.00  --qbf_dom_inst                          none
% 11.74/2.00  --qbf_dom_pre_inst                      false
% 11.74/2.00  --qbf_sk_in                             false
% 11.74/2.00  --qbf_pred_elim                         true
% 11.74/2.00  --qbf_split                             512
% 11.74/2.00  
% 11.74/2.00  ------ BMC1 Options
% 11.74/2.00  
% 11.74/2.00  --bmc1_incremental                      false
% 11.74/2.00  --bmc1_axioms                           reachable_all
% 11.74/2.00  --bmc1_min_bound                        0
% 11.74/2.00  --bmc1_max_bound                        -1
% 11.74/2.00  --bmc1_max_bound_default                -1
% 11.74/2.00  --bmc1_symbol_reachability              true
% 11.74/2.00  --bmc1_property_lemmas                  false
% 11.74/2.00  --bmc1_k_induction                      false
% 11.74/2.00  --bmc1_non_equiv_states                 false
% 11.74/2.00  --bmc1_deadlock                         false
% 11.74/2.00  --bmc1_ucm                              false
% 11.74/2.00  --bmc1_add_unsat_core                   none
% 11.74/2.00  --bmc1_unsat_core_children              false
% 11.74/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/2.00  --bmc1_out_stat                         full
% 11.74/2.00  --bmc1_ground_init                      false
% 11.74/2.00  --bmc1_pre_inst_next_state              false
% 11.74/2.00  --bmc1_pre_inst_state                   false
% 11.74/2.00  --bmc1_pre_inst_reach_state             false
% 11.74/2.00  --bmc1_out_unsat_core                   false
% 11.74/2.00  --bmc1_aig_witness_out                  false
% 11.74/2.00  --bmc1_verbose                          false
% 11.74/2.00  --bmc1_dump_clauses_tptp                false
% 11.74/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.74/2.00  --bmc1_dump_file                        -
% 11.74/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.74/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.74/2.00  --bmc1_ucm_extend_mode                  1
% 11.74/2.00  --bmc1_ucm_init_mode                    2
% 11.74/2.00  --bmc1_ucm_cone_mode                    none
% 11.74/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.74/2.00  --bmc1_ucm_relax_model                  4
% 11.74/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.74/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/2.00  --bmc1_ucm_layered_model                none
% 11.74/2.00  --bmc1_ucm_max_lemma_size               10
% 11.74/2.00  
% 11.74/2.00  ------ AIG Options
% 11.74/2.00  
% 11.74/2.00  --aig_mode                              false
% 11.74/2.00  
% 11.74/2.00  ------ Instantiation Options
% 11.74/2.00  
% 11.74/2.00  --instantiation_flag                    true
% 11.74/2.00  --inst_sos_flag                         false
% 11.74/2.00  --inst_sos_phase                        true
% 11.74/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/2.00  --inst_lit_sel_side                     num_symb
% 11.74/2.00  --inst_solver_per_active                1400
% 11.74/2.00  --inst_solver_calls_frac                1.
% 11.74/2.00  --inst_passive_queue_type               priority_queues
% 11.74/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.74/2.00  --inst_passive_queues_freq              [25;2]
% 11.74/2.00  --inst_dismatching                      true
% 11.74/2.00  --inst_eager_unprocessed_to_passive     true
% 11.74/2.00  --inst_prop_sim_given                   true
% 11.74/2.00  --inst_prop_sim_new                     false
% 11.74/2.00  --inst_subs_new                         false
% 11.74/2.00  --inst_eq_res_simp                      false
% 11.74/2.00  --inst_subs_given                       false
% 11.74/2.00  --inst_orphan_elimination               true
% 11.74/2.00  --inst_learning_loop_flag               true
% 11.74/2.00  --inst_learning_start                   3000
% 11.74/2.00  --inst_learning_factor                  2
% 11.74/2.00  --inst_start_prop_sim_after_learn       3
% 11.74/2.00  --inst_sel_renew                        solver
% 11.74/2.00  --inst_lit_activity_flag                true
% 11.74/2.00  --inst_restr_to_given                   false
% 11.74/2.00  --inst_activity_threshold               500
% 11.74/2.00  --inst_out_proof                        true
% 11.74/2.00  
% 11.74/2.00  ------ Resolution Options
% 11.74/2.00  
% 11.74/2.00  --resolution_flag                       true
% 11.74/2.00  --res_lit_sel                           adaptive
% 11.74/2.00  --res_lit_sel_side                      none
% 11.74/2.00  --res_ordering                          kbo
% 11.74/2.00  --res_to_prop_solver                    active
% 11.74/2.00  --res_prop_simpl_new                    false
% 11.74/2.00  --res_prop_simpl_given                  true
% 11.74/2.00  --res_passive_queue_type                priority_queues
% 11.74/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.74/2.00  --res_passive_queues_freq               [15;5]
% 11.74/2.00  --res_forward_subs                      full
% 11.74/2.00  --res_backward_subs                     full
% 11.74/2.00  --res_forward_subs_resolution           true
% 11.74/2.00  --res_backward_subs_resolution          true
% 11.74/2.00  --res_orphan_elimination                true
% 11.74/2.00  --res_time_limit                        2.
% 11.74/2.00  --res_out_proof                         true
% 11.74/2.00  
% 11.74/2.00  ------ Superposition Options
% 11.74/2.00  
% 11.74/2.00  --superposition_flag                    true
% 11.74/2.00  --sup_passive_queue_type                priority_queues
% 11.74/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.74/2.00  --demod_completeness_check              fast
% 11.74/2.00  --demod_use_ground                      true
% 11.74/2.00  --sup_to_prop_solver                    passive
% 11.74/2.00  --sup_prop_simpl_new                    true
% 11.74/2.00  --sup_prop_simpl_given                  true
% 11.74/2.00  --sup_fun_splitting                     false
% 11.74/2.00  --sup_smt_interval                      50000
% 11.74/2.00  
% 11.74/2.00  ------ Superposition Simplification Setup
% 11.74/2.00  
% 11.74/2.00  --sup_indices_passive                   []
% 11.74/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_full_bw                           [BwDemod]
% 11.74/2.00  --sup_immed_triv                        [TrivRules]
% 11.74/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_immed_bw_main                     []
% 11.74/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/2.00  
% 11.74/2.00  ------ Combination Options
% 11.74/2.00  
% 11.74/2.00  --comb_res_mult                         3
% 11.74/2.00  --comb_sup_mult                         2
% 11.74/2.00  --comb_inst_mult                        10
% 11.74/2.00  
% 11.74/2.00  ------ Debug Options
% 11.74/2.00  
% 11.74/2.00  --dbg_backtrace                         false
% 11.74/2.00  --dbg_dump_prop_clauses                 false
% 11.74/2.00  --dbg_dump_prop_clauses_file            -
% 11.74/2.00  --dbg_out_stat                          false
% 11.74/2.00  ------ Parsing...
% 11.74/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.74/2.00  ------ Proving...
% 11.74/2.00  ------ Problem Properties 
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  clauses                                 18
% 11.74/2.00  conjectures                             0
% 11.74/2.00  EPR                                     3
% 11.74/2.00  Horn                                    12
% 11.74/2.00  unary                                   4
% 11.74/2.00  binary                                  5
% 11.74/2.00  lits                                    44
% 11.74/2.00  lits eq                                 9
% 11.74/2.00  fd_pure                                 0
% 11.74/2.00  fd_pseudo                               0
% 11.74/2.00  fd_cond                                 0
% 11.74/2.00  fd_pseudo_cond                          6
% 11.74/2.00  AC symbols                              0
% 11.74/2.00  
% 11.74/2.00  ------ Schedule dynamic 5 is on 
% 11.74/2.00  
% 11.74/2.00  ------ no conjectures: strip conj schedule 
% 11.74/2.00  
% 11.74/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  ------ 
% 11.74/2.00  Current options:
% 11.74/2.00  ------ 
% 11.74/2.00  
% 11.74/2.00  ------ Input Options
% 11.74/2.00  
% 11.74/2.00  --out_options                           all
% 11.74/2.00  --tptp_safe_out                         true
% 11.74/2.00  --problem_path                          ""
% 11.74/2.00  --include_path                          ""
% 11.74/2.00  --clausifier                            res/vclausify_rel
% 11.74/2.00  --clausifier_options                    --mode clausify
% 11.74/2.00  --stdin                                 false
% 11.74/2.00  --stats_out                             all
% 11.74/2.00  
% 11.74/2.00  ------ General Options
% 11.74/2.00  
% 11.74/2.00  --fof                                   false
% 11.74/2.00  --time_out_real                         305.
% 11.74/2.00  --time_out_virtual                      -1.
% 11.74/2.00  --symbol_type_check                     false
% 11.74/2.00  --clausify_out                          false
% 11.74/2.00  --sig_cnt_out                           false
% 11.74/2.00  --trig_cnt_out                          false
% 11.74/2.00  --trig_cnt_out_tolerance                1.
% 11.74/2.00  --trig_cnt_out_sk_spl                   false
% 11.74/2.00  --abstr_cl_out                          false
% 11.74/2.00  
% 11.74/2.00  ------ Global Options
% 11.74/2.00  
% 11.74/2.00  --schedule                              default
% 11.74/2.00  --add_important_lit                     false
% 11.74/2.00  --prop_solver_per_cl                    1000
% 11.74/2.00  --min_unsat_core                        false
% 11.74/2.00  --soft_assumptions                      false
% 11.74/2.00  --soft_lemma_size                       3
% 11.74/2.00  --prop_impl_unit_size                   0
% 11.74/2.00  --prop_impl_unit                        []
% 11.74/2.00  --share_sel_clauses                     true
% 11.74/2.00  --reset_solvers                         false
% 11.74/2.00  --bc_imp_inh                            [conj_cone]
% 11.74/2.00  --conj_cone_tolerance                   3.
% 11.74/2.00  --extra_neg_conj                        none
% 11.74/2.00  --large_theory_mode                     true
% 11.74/2.00  --prolific_symb_bound                   200
% 11.74/2.00  --lt_threshold                          2000
% 11.74/2.00  --clause_weak_htbl                      true
% 11.74/2.00  --gc_record_bc_elim                     false
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing Options
% 11.74/2.00  
% 11.74/2.00  --preprocessing_flag                    true
% 11.74/2.00  --time_out_prep_mult                    0.1
% 11.74/2.00  --splitting_mode                        input
% 11.74/2.00  --splitting_grd                         true
% 11.74/2.00  --splitting_cvd                         false
% 11.74/2.00  --splitting_cvd_svl                     false
% 11.74/2.00  --splitting_nvd                         32
% 11.74/2.00  --sub_typing                            true
% 11.74/2.00  --prep_gs_sim                           true
% 11.74/2.00  --prep_unflatten                        true
% 11.74/2.00  --prep_res_sim                          true
% 11.74/2.00  --prep_upred                            true
% 11.74/2.00  --prep_sem_filter                       exhaustive
% 11.74/2.00  --prep_sem_filter_out                   false
% 11.74/2.00  --pred_elim                             true
% 11.74/2.00  --res_sim_input                         true
% 11.74/2.00  --eq_ax_congr_red                       true
% 11.74/2.00  --pure_diseq_elim                       true
% 11.74/2.00  --brand_transform                       false
% 11.74/2.00  --non_eq_to_eq                          false
% 11.74/2.00  --prep_def_merge                        true
% 11.74/2.00  --prep_def_merge_prop_impl              false
% 11.74/2.00  --prep_def_merge_mbd                    true
% 11.74/2.00  --prep_def_merge_tr_red                 false
% 11.74/2.00  --prep_def_merge_tr_cl                  false
% 11.74/2.00  --smt_preprocessing                     true
% 11.74/2.00  --smt_ac_axioms                         fast
% 11.74/2.00  --preprocessed_out                      false
% 11.74/2.00  --preprocessed_stats                    false
% 11.74/2.00  
% 11.74/2.00  ------ Abstraction refinement Options
% 11.74/2.00  
% 11.74/2.00  --abstr_ref                             []
% 11.74/2.00  --abstr_ref_prep                        false
% 11.74/2.00  --abstr_ref_until_sat                   false
% 11.74/2.00  --abstr_ref_sig_restrict                funpre
% 11.74/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/2.00  --abstr_ref_under                       []
% 11.74/2.00  
% 11.74/2.00  ------ SAT Options
% 11.74/2.00  
% 11.74/2.00  --sat_mode                              false
% 11.74/2.00  --sat_fm_restart_options                ""
% 11.74/2.00  --sat_gr_def                            false
% 11.74/2.00  --sat_epr_types                         true
% 11.74/2.00  --sat_non_cyclic_types                  false
% 11.74/2.00  --sat_finite_models                     false
% 11.74/2.00  --sat_fm_lemmas                         false
% 11.74/2.00  --sat_fm_prep                           false
% 11.74/2.00  --sat_fm_uc_incr                        true
% 11.74/2.00  --sat_out_model                         small
% 11.74/2.00  --sat_out_clauses                       false
% 11.74/2.00  
% 11.74/2.00  ------ QBF Options
% 11.74/2.00  
% 11.74/2.00  --qbf_mode                              false
% 11.74/2.00  --qbf_elim_univ                         false
% 11.74/2.00  --qbf_dom_inst                          none
% 11.74/2.00  --qbf_dom_pre_inst                      false
% 11.74/2.00  --qbf_sk_in                             false
% 11.74/2.00  --qbf_pred_elim                         true
% 11.74/2.00  --qbf_split                             512
% 11.74/2.00  
% 11.74/2.00  ------ BMC1 Options
% 11.74/2.00  
% 11.74/2.00  --bmc1_incremental                      false
% 11.74/2.00  --bmc1_axioms                           reachable_all
% 11.74/2.00  --bmc1_min_bound                        0
% 11.74/2.00  --bmc1_max_bound                        -1
% 11.74/2.00  --bmc1_max_bound_default                -1
% 11.74/2.00  --bmc1_symbol_reachability              true
% 11.74/2.00  --bmc1_property_lemmas                  false
% 11.74/2.00  --bmc1_k_induction                      false
% 11.74/2.00  --bmc1_non_equiv_states                 false
% 11.74/2.00  --bmc1_deadlock                         false
% 11.74/2.00  --bmc1_ucm                              false
% 11.74/2.00  --bmc1_add_unsat_core                   none
% 11.74/2.00  --bmc1_unsat_core_children              false
% 11.74/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/2.00  --bmc1_out_stat                         full
% 11.74/2.00  --bmc1_ground_init                      false
% 11.74/2.00  --bmc1_pre_inst_next_state              false
% 11.74/2.00  --bmc1_pre_inst_state                   false
% 11.74/2.00  --bmc1_pre_inst_reach_state             false
% 11.74/2.00  --bmc1_out_unsat_core                   false
% 11.74/2.00  --bmc1_aig_witness_out                  false
% 11.74/2.00  --bmc1_verbose                          false
% 11.74/2.00  --bmc1_dump_clauses_tptp                false
% 11.74/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.74/2.00  --bmc1_dump_file                        -
% 11.74/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.74/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.74/2.00  --bmc1_ucm_extend_mode                  1
% 11.74/2.00  --bmc1_ucm_init_mode                    2
% 11.74/2.00  --bmc1_ucm_cone_mode                    none
% 11.74/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.74/2.00  --bmc1_ucm_relax_model                  4
% 11.74/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.74/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/2.00  --bmc1_ucm_layered_model                none
% 11.74/2.00  --bmc1_ucm_max_lemma_size               10
% 11.74/2.00  
% 11.74/2.00  ------ AIG Options
% 11.74/2.00  
% 11.74/2.00  --aig_mode                              false
% 11.74/2.00  
% 11.74/2.00  ------ Instantiation Options
% 11.74/2.00  
% 11.74/2.00  --instantiation_flag                    true
% 11.74/2.00  --inst_sos_flag                         false
% 11.74/2.00  --inst_sos_phase                        true
% 11.74/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/2.00  --inst_lit_sel_side                     none
% 11.74/2.00  --inst_solver_per_active                1400
% 11.74/2.00  --inst_solver_calls_frac                1.
% 11.74/2.00  --inst_passive_queue_type               priority_queues
% 11.74/2.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 11.74/2.00  --inst_passive_queues_freq              [25;2]
% 11.74/2.00  --inst_dismatching                      true
% 11.74/2.00  --inst_eager_unprocessed_to_passive     true
% 11.74/2.00  --inst_prop_sim_given                   true
% 11.74/2.00  --inst_prop_sim_new                     false
% 11.74/2.00  --inst_subs_new                         false
% 11.74/2.00  --inst_eq_res_simp                      false
% 11.74/2.00  --inst_subs_given                       false
% 11.74/2.00  --inst_orphan_elimination               true
% 11.74/2.00  --inst_learning_loop_flag               true
% 11.74/2.00  --inst_learning_start                   3000
% 11.74/2.00  --inst_learning_factor                  2
% 11.74/2.00  --inst_start_prop_sim_after_learn       3
% 11.74/2.00  --inst_sel_renew                        solver
% 11.74/2.00  --inst_lit_activity_flag                true
% 11.74/2.00  --inst_restr_to_given                   false
% 11.74/2.00  --inst_activity_threshold               500
% 11.74/2.00  --inst_out_proof                        true
% 11.74/2.00  
% 11.74/2.00  ------ Resolution Options
% 11.74/2.00  
% 11.74/2.00  --resolution_flag                       false
% 11.74/2.00  --res_lit_sel                           adaptive
% 11.74/2.00  --res_lit_sel_side                      none
% 11.74/2.00  --res_ordering                          kbo
% 11.74/2.00  --res_to_prop_solver                    active
% 11.74/2.00  --res_prop_simpl_new                    false
% 11.74/2.00  --res_prop_simpl_given                  true
% 11.74/2.00  --res_passive_queue_type                priority_queues
% 11.74/2.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 11.74/2.00  --res_passive_queues_freq               [15;5]
% 11.74/2.00  --res_forward_subs                      full
% 11.74/2.00  --res_backward_subs                     full
% 11.74/2.00  --res_forward_subs_resolution           true
% 11.74/2.00  --res_backward_subs_resolution          true
% 11.74/2.00  --res_orphan_elimination                true
% 11.74/2.00  --res_time_limit                        2.
% 11.74/2.00  --res_out_proof                         true
% 11.74/2.00  
% 11.74/2.00  ------ Superposition Options
% 11.74/2.00  
% 11.74/2.00  --superposition_flag                    true
% 11.74/2.00  --sup_passive_queue_type                priority_queues
% 11.74/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.74/2.00  --demod_completeness_check              fast
% 11.74/2.00  --demod_use_ground                      true
% 11.74/2.00  --sup_to_prop_solver                    passive
% 11.74/2.00  --sup_prop_simpl_new                    true
% 11.74/2.00  --sup_prop_simpl_given                  true
% 11.74/2.00  --sup_fun_splitting                     false
% 11.74/2.00  --sup_smt_interval                      50000
% 11.74/2.00  
% 11.74/2.00  ------ Superposition Simplification Setup
% 11.74/2.00  
% 11.74/2.00  --sup_indices_passive                   []
% 11.74/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_full_bw                           [BwDemod]
% 11.74/2.00  --sup_immed_triv                        [TrivRules]
% 11.74/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_immed_bw_main                     []
% 11.74/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/2.00  
% 11.74/2.00  ------ Combination Options
% 11.74/2.00  
% 11.74/2.00  --comb_res_mult                         3
% 11.74/2.00  --comb_sup_mult                         2
% 11.74/2.00  --comb_inst_mult                        10
% 11.74/2.00  
% 11.74/2.00  ------ Debug Options
% 11.74/2.00  
% 11.74/2.00  --dbg_backtrace                         false
% 11.74/2.00  --dbg_dump_prop_clauses                 false
% 11.74/2.00  --dbg_dump_prop_clauses_file            -
% 11.74/2.00  --dbg_out_stat                          false
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  ------ Proving...
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  % SZS status Theorem for theBenchmark.p
% 11.74/2.00  
% 11.74/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.74/2.00  
% 11.74/2.00  fof(f9,axiom,(
% 11.74/2.00    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f23,plain,(
% 11.74/2.00    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(ennf_transformation,[],[f9])).
% 11.74/2.00  
% 11.74/2.00  fof(f47,plain,(
% 11.74/2.00    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(nnf_transformation,[],[f23])).
% 11.74/2.00  
% 11.74/2.00  fof(f48,plain,(
% 11.74/2.00    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(rectify,[],[f47])).
% 11.74/2.00  
% 11.74/2.00  fof(f49,plain,(
% 11.74/2.00    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & ~r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) & sK7(X0) != sK8(X0) & r2_hidden(sK8(X0),k3_relat_1(X0)) & r2_hidden(sK7(X0),k3_relat_1(X0))))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f50,plain,(
% 11.74/2.00    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & ~r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) & sK7(X0) != sK8(X0) & r2_hidden(sK8(X0),k3_relat_1(X0)) & r2_hidden(sK7(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f48,f49])).
% 11.74/2.00  
% 11.74/2.00  fof(f83,plain,(
% 11.74/2.00    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f50])).
% 11.74/2.00  
% 11.74/2.00  fof(f10,conjecture,(
% 11.74/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f11,negated_conjecture,(
% 11.74/2.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 11.74/2.00    inference(negated_conjecture,[],[f10])).
% 11.74/2.00  
% 11.74/2.00  fof(f24,plain,(
% 11.74/2.00    ? [X0,X1,X2] : ((~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 11.74/2.00    inference(ennf_transformation,[],[f11])).
% 11.74/2.00  
% 11.74/2.00  fof(f25,plain,(
% 11.74/2.00    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 11.74/2.00    inference(flattening,[],[f24])).
% 11.74/2.00  
% 11.74/2.00  fof(f51,plain,(
% 11.74/2.00    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) & v2_wellord1(sK11) & v1_relat_1(sK11))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f52,plain,(
% 11.74/2.00    ~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) & v2_wellord1(sK11) & v1_relat_1(sK11)),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f25,f51])).
% 11.74/2.00  
% 11.74/2.00  fof(f89,plain,(
% 11.74/2.00    v1_relat_1(sK11)),
% 11.74/2.00    inference(cnf_transformation,[],[f52])).
% 11.74/2.00  
% 11.74/2.00  fof(f6,axiom,(
% 11.74/2.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f18,plain,(
% 11.74/2.00    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(ennf_transformation,[],[f6])).
% 11.74/2.00  
% 11.74/2.00  fof(f37,plain,(
% 11.74/2.00    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(nnf_transformation,[],[f18])).
% 11.74/2.00  
% 11.74/2.00  fof(f38,plain,(
% 11.74/2.00    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(flattening,[],[f37])).
% 11.74/2.00  
% 11.74/2.00  fof(f72,plain,(
% 11.74/2.00    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f38])).
% 11.74/2.00  
% 11.74/2.00  fof(f90,plain,(
% 11.74/2.00    v2_wellord1(sK11)),
% 11.74/2.00    inference(cnf_transformation,[],[f52])).
% 11.74/2.00  
% 11.74/2.00  fof(f1,axiom,(
% 11.74/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f13,plain,(
% 11.74/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.74/2.00    inference(ennf_transformation,[],[f1])).
% 11.74/2.00  
% 11.74/2.00  fof(f26,plain,(
% 11.74/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.74/2.00    inference(nnf_transformation,[],[f13])).
% 11.74/2.00  
% 11.74/2.00  fof(f27,plain,(
% 11.74/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.74/2.00    inference(rectify,[],[f26])).
% 11.74/2.00  
% 11.74/2.00  fof(f28,plain,(
% 11.74/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f29,plain,(
% 11.74/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.74/2.00  
% 11.74/2.00  fof(f54,plain,(
% 11.74/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f29])).
% 11.74/2.00  
% 11.74/2.00  fof(f5,axiom,(
% 11.74/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f17,plain,(
% 11.74/2.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(ennf_transformation,[],[f5])).
% 11.74/2.00  
% 11.74/2.00  fof(f32,plain,(
% 11.74/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(nnf_transformation,[],[f17])).
% 11.74/2.00  
% 11.74/2.00  fof(f33,plain,(
% 11.74/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(flattening,[],[f32])).
% 11.74/2.00  
% 11.74/2.00  fof(f34,plain,(
% 11.74/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(rectify,[],[f33])).
% 11.74/2.00  
% 11.74/2.00  fof(f35,plain,(
% 11.74/2.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f36,plain,(
% 11.74/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 11.74/2.00  
% 11.74/2.00  fof(f64,plain,(
% 11.74/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f36])).
% 11.74/2.00  
% 11.74/2.00  fof(f95,plain,(
% 11.74/2.00    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(equality_resolution,[],[f64])).
% 11.74/2.00  
% 11.74/2.00  fof(f7,axiom,(
% 11.74/2.00    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f19,plain,(
% 11.74/2.00    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(ennf_transformation,[],[f7])).
% 11.74/2.00  
% 11.74/2.00  fof(f20,plain,(
% 11.74/2.00    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(flattening,[],[f19])).
% 11.74/2.00  
% 11.74/2.00  fof(f39,plain,(
% 11.74/2.00    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(nnf_transformation,[],[f20])).
% 11.74/2.00  
% 11.74/2.00  fof(f40,plain,(
% 11.74/2.00    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(rectify,[],[f39])).
% 11.74/2.00  
% 11.74/2.00  fof(f41,plain,(
% 11.74/2.00    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f42,plain,(
% 11.74/2.00    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f41])).
% 11.74/2.00  
% 11.74/2.00  fof(f75,plain,(
% 11.74/2.00    ( ! [X6,X4,X0,X5] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f42])).
% 11.74/2.00  
% 11.74/2.00  fof(f70,plain,(
% 11.74/2.00    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f38])).
% 11.74/2.00  
% 11.74/2.00  fof(f4,axiom,(
% 11.74/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f15,plain,(
% 11.74/2.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 11.74/2.00    inference(ennf_transformation,[],[f4])).
% 11.74/2.00  
% 11.74/2.00  fof(f16,plain,(
% 11.74/2.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 11.74/2.00    inference(flattening,[],[f15])).
% 11.74/2.00  
% 11.74/2.00  fof(f61,plain,(
% 11.74/2.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f16])).
% 11.74/2.00  
% 11.74/2.00  fof(f65,plain,(
% 11.74/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f36])).
% 11.74/2.00  
% 11.74/2.00  fof(f94,plain,(
% 11.74/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(equality_resolution,[],[f65])).
% 11.74/2.00  
% 11.74/2.00  fof(f55,plain,(
% 11.74/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f29])).
% 11.74/2.00  
% 11.74/2.00  fof(f3,axiom,(
% 11.74/2.00    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f12,plain,(
% 11.74/2.00    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 11.74/2.00    inference(unused_predicate_definition_removal,[],[f3])).
% 11.74/2.00  
% 11.74/2.00  fof(f14,plain,(
% 11.74/2.00    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 11.74/2.00    inference(ennf_transformation,[],[f12])).
% 11.74/2.00  
% 11.74/2.00  fof(f60,plain,(
% 11.74/2.00    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f14])).
% 11.74/2.00  
% 11.74/2.00  fof(f91,plain,(
% 11.74/2.00    ~r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))),
% 11.74/2.00    inference(cnf_transformation,[],[f52])).
% 11.74/2.00  
% 11.74/2.00  fof(f59,plain,(
% 11.74/2.00    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f14])).
% 11.74/2.00  
% 11.74/2.00  fof(f8,axiom,(
% 11.74/2.00    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f21,plain,(
% 11.74/2.00    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(ennf_transformation,[],[f8])).
% 11.74/2.00  
% 11.74/2.00  fof(f22,plain,(
% 11.74/2.00    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(flattening,[],[f21])).
% 11.74/2.00  
% 11.74/2.00  fof(f43,plain,(
% 11.74/2.00    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(nnf_transformation,[],[f22])).
% 11.74/2.00  
% 11.74/2.00  fof(f44,plain,(
% 11.74/2.00    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(rectify,[],[f43])).
% 11.74/2.00  
% 11.74/2.00  fof(f45,plain,(
% 11.74/2.00    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK5(X0) != sK6(X0) & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)))),
% 11.74/2.00    introduced(choice_axiom,[])).
% 11.74/2.00  
% 11.74/2.00  fof(f46,plain,(
% 11.74/2.00    ! [X0] : (((v4_relat_2(X0) | (sK5(X0) != sK6(X0) & r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 11.74/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f45])).
% 11.74/2.00  
% 11.74/2.00  fof(f79,plain,(
% 11.74/2.00    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f46])).
% 11.74/2.00  
% 11.74/2.00  fof(f71,plain,(
% 11.74/2.00    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f38])).
% 11.74/2.00  
% 11.74/2.00  fof(f63,plain,(
% 11.74/2.00    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f36])).
% 11.74/2.00  
% 11.74/2.00  fof(f96,plain,(
% 11.74/2.00    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(equality_resolution,[],[f63])).
% 11.74/2.00  
% 11.74/2.00  fof(f97,plain,(
% 11.74/2.00    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 11.74/2.00    inference(equality_resolution,[],[f96])).
% 11.74/2.00  
% 11.74/2.00  fof(f2,axiom,(
% 11.74/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.74/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/2.00  
% 11.74/2.00  fof(f30,plain,(
% 11.74/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.74/2.00    inference(nnf_transformation,[],[f2])).
% 11.74/2.00  
% 11.74/2.00  fof(f31,plain,(
% 11.74/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.74/2.00    inference(flattening,[],[f30])).
% 11.74/2.00  
% 11.74/2.00  fof(f56,plain,(
% 11.74/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.74/2.00    inference(cnf_transformation,[],[f31])).
% 11.74/2.00  
% 11.74/2.00  fof(f93,plain,(
% 11.74/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.74/2.00    inference(equality_resolution,[],[f56])).
% 11.74/2.00  
% 11.74/2.00  fof(f62,plain,(
% 11.74/2.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f16])).
% 11.74/2.00  
% 11.74/2.00  fof(f58,plain,(
% 11.74/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.74/2.00    inference(cnf_transformation,[],[f31])).
% 11.74/2.00  
% 11.74/2.00  cnf(c_35,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 11.74/2.00      | ~ v6_relat_2(X1)
% 11.74/2.00      | ~ v1_relat_1(X1)
% 11.74/2.00      | X0 = X2 ),
% 11.74/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_38,negated_conjecture,
% 11.74/2.00      ( v1_relat_1(sK11) ),
% 11.74/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_871,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | ~ v6_relat_2(X1)
% 11.74/2.00      | X2 = X0
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_35,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_872,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | ~ v6_relat_2(sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_871]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_18,plain,
% 11.74/2.00      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 11.74/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_37,negated_conjecture,
% 11.74/2.00      ( v2_wellord1(sK11) ),
% 11.74/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_458,plain,
% 11.74/2.00      ( v6_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_459,plain,
% 11.74/2.00      ( v6_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_458]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_92,plain,
% 11.74/2.00      ( v6_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_461,plain,
% 11.74/2.00      ( v6_relat_2(sK11) ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_459,c_38,c_37,c_92]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_804,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | ~ v1_relat_1(X1)
% 11.74/2.00      | X2 = X0
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_35,c_461]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_805,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | ~ v1_relat_1(sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_804]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_809,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_805,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_810,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_809]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_875,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_872,c_38,c_805]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_876,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(X1,k3_relat_1(sK11))
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_875]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1530,plain,
% 11.74/2.00      ( X0 = X1
% 11.74/2.00      | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1,plain,
% 11.74/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1538,plain,
% 11.74/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.74/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_14,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | ~ v1_relat_1(X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_904,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_905,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_904]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1528,plain,
% 11.74/2.00      ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2195,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X0),sK11) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_1538,c_1528]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_25,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 11.74/2.00      | r2_hidden(k4_tarski(X3,X1),X2)
% 11.74/2.00      | ~ v8_relat_2(X2)
% 11.74/2.00      | ~ v1_relat_1(X2) ),
% 11.74/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1036,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 11.74/2.00      | r2_hidden(k4_tarski(X3,X1),X2)
% 11.74/2.00      | ~ v8_relat_2(X2)
% 11.74/2.00      | sK11 != X2 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_25,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1037,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X1),sK11)
% 11.74/2.00      | ~ v8_relat_2(sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_1036]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_20,plain,
% 11.74/2.00      ( v8_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 11.74/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_436,plain,
% 11.74/2.00      ( v8_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_20,c_37]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_437,plain,
% 11.74/2.00      ( v8_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_436]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_86,plain,
% 11.74/2.00      ( v8_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_439,plain,
% 11.74/2.00      ( v8_relat_2(sK11) ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_437,c_38,c_37,c_86]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_634,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X3,X0),X2)
% 11.74/2.00      | r2_hidden(k4_tarski(X3,X1),X2)
% 11.74/2.00      | ~ v1_relat_1(X2)
% 11.74/2.00      | sK11 != X2 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_25,c_439]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_635,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X1),sK11)
% 11.74/2.00      | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_634]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_637,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X2,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_635,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_638,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X1),sK11) ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_637]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1039,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X2,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_1037,c_38,c_635]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1040,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X1),sK11) ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_1039]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1531,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X1),sK11) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2633,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,X1),X2)),sK11) != iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X1),X2) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_2195,c_1531]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_3938,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 11.74/2.00      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_1530,c_2633]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_9,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | ~ v1_relat_1(X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_927,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_928,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_927]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1526,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(sK11)) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2635,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k3_relat_1(sK11)) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_2195,c_1526]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_19473,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | sK0(k1_wellord1(sK11,X0),X1) = X2
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_3938,c_2635]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_19474,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 11.74/2.00      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,X0),X1),X2),sK11) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_19473]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_13,plain,
% 11.74/2.00      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | ~ v1_relat_1(X1)
% 11.74/2.00      | X0 = X2 ),
% 11.74/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_914,plain,
% 11.74/2.00      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.74/2.00      | X2 = X0
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_915,plain,
% 11.74/2.00      ( r2_hidden(X0,k1_wellord1(sK11,X1))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | X1 = X0 ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_914]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1527,plain,
% 11.74/2.00      ( X0 = X1
% 11.74/2.00      | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_19483,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,X0),X1) = X2
% 11.74/2.00      | r2_hidden(X2,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X2,X0),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,X0),X1),k1_wellord1(sK11,X2)) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_19474,c_1527]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_0,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1539,plain,
% 11.74/2.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.74/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_48301,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = X1
% 11.74/2.00      | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,X0),k1_wellord1(sK11,X1)) = iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_19483,c_1539]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_6,plain,
% 11.74/2.00      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.74/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_36,negated_conjecture,
% 11.74/2.00      ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_424,plain,
% 11.74/2.00      ( ~ r1_tarski(X0,X1)
% 11.74/2.00      | k1_wellord1(sK11,sK10) != X0
% 11.74/2.00      | k1_wellord1(sK11,sK9) != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_36]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_425,plain,
% 11.74/2.00      ( ~ r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_424]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1533,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_48985,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) = sK9
% 11.74/2.00      | r2_hidden(k4_tarski(sK9,sK10),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_48301,c_1533]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7,plain,
% 11.74/2.00      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_417,plain,
% 11.74/2.00      ( ~ r1_tarski(X0,X1)
% 11.74/2.00      | k1_wellord1(sK11,sK10) != X1
% 11.74/2.00      | k1_wellord1(sK11,sK9) != X0 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_7,c_36]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_418,plain,
% 11.74/2.00      ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_417]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1534,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_48984,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
% 11.74/2.00      | r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top ),
% 11.74/2.00      inference(superposition,[status(thm)],[c_48301,c_1534]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1221,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.74/2.00      theory(equality) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_5352,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,X1)
% 11.74/2.00      | r2_hidden(X2,k1_wellord1(sK11,X2))
% 11.74/2.00      | X2 != X0
% 11.74/2.00      | k1_wellord1(sK11,X2) != X1 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1221]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_12985,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
% 11.74/2.00      | r2_hidden(X1,k1_wellord1(sK11,X1))
% 11.74/2.00      | X1 != X0
% 11.74/2.00      | k1_wellord1(sK11,X1) != k1_wellord1(sK11,X1) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_5352]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_43391,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK10))
% 11.74/2.00      | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_12985]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1224,plain,
% 11.74/2.00      ( X0 != X1 | X2 != X3 | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
% 11.74/2.00      theory(equality) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2024,plain,
% 11.74/2.00      ( X0 != sK9
% 11.74/2.00      | X1 != sK11
% 11.74/2.00      | k1_wellord1(X1,X0) = k1_wellord1(sK11,sK9) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1224]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_43074,plain,
% 11.74/2.00      ( X0 != sK11
% 11.74/2.00      | k1_wellord1(X0,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) = k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != sK9 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2024]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_43080,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) = k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != sK9
% 11.74/2.00      | sK11 != sK11 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_43074]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1219,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2101,plain,
% 11.74/2.00      ( X0 != X1 | sK10 != X1 | sK10 = X0 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1219]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_4906,plain,
% 11.74/2.00      ( X0 != sK10 | sK10 = X0 | sK10 != sK10 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2101]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_35903,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK10
% 11.74/2.00      | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | sK10 != sK10 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_4906]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1697,plain,
% 11.74/2.00      ( r2_hidden(X0,X1)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | X1 != k1_wellord1(sK11,sK9)
% 11.74/2.00      | X0 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1221]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_6887,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | r2_hidden(sK10,X0)
% 11.74/2.00      | X0 != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1697]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_33651,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK9))
% 11.74/2.00      | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_6887]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_33656,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_33651]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_22863,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))))
% 11.74/2.00      | k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_6887]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_22864,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_22863]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2740,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),X0)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | X0 != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1697]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_4065,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,X0))
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | k1_wellord1(sK11,X0) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2740]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_13902,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))))
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_4065]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_3553,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK10,X0),sK11)
% 11.74/2.00      | ~ r2_hidden(sK10,k1_wellord1(sK11,X0)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_905]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7970,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
% 11.74/2.00      | ~ r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_3553]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7972,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_7970]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_29,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 11.74/2.00      | ~ v4_relat_2(X2)
% 11.74/2.00      | ~ v1_relat_1(X2)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1019,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 11.74/2.00      | ~ v4_relat_2(X2)
% 11.74/2.00      | X1 = X0
% 11.74/2.00      | sK11 != X2 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1020,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | ~ v4_relat_2(sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_1019]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_19,plain,
% 11.74/2.00      ( v4_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 11.74/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_447,plain,
% 11.74/2.00      ( v4_relat_2(X0) | ~ v1_relat_1(X0) | sK11 != X0 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_19,c_37]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_448,plain,
% 11.74/2.00      ( v4_relat_2(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_447]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_89,plain,
% 11.74/2.00      ( v4_relat_2(sK11) | ~ v2_wellord1(sK11) | ~ v1_relat_1(sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_450,plain,
% 11.74/2.00      ( v4_relat_2(sK11) ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_448,c_38,c_37,c_89]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_538,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 11.74/2.00      | ~ v1_relat_1(X2)
% 11.74/2.00      | X1 = X0
% 11.74/2.00      | sK11 != X2 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_29,c_450]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_539,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | ~ v1_relat_1(sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_538]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1022,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | X0 = X1 ),
% 11.74/2.00      inference(global_propositional_subsumption,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_1020,c_38,c_539]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1023,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),sK11)
% 11.74/2.00      | X1 = X0 ),
% 11.74/2.00      inference(renaming,[status(thm)],[c_1022]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2966,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,sK9),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK9,X0),sK11)
% 11.74/2.00      | X0 = sK9 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7965,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
% 11.74/2.00      | sK10 = sK9 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2966]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7968,plain,
% 11.74/2.00      ( sK10 = sK9
% 11.74/2.00      | r2_hidden(k4_tarski(sK10,sK9),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_7965]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7964,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK10,sK9),sK11)
% 11.74/2.00      | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_3553]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7966,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_7964]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2085,plain,
% 11.74/2.00      ( r2_hidden(X0,k1_wellord1(sK11,sK10))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X0,sK10),sK11)
% 11.74/2.00      | sK10 = X0 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_915]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7553,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11)
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
% 11.74/2.00      | sK10 = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2085]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1825,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(X0,sK10),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1040]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7547,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
% 11.74/2.00      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK10),sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1825]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2296,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),X0),sK11)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,X0)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_905]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_7546,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2296]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_6916,plain,
% 11.74/2.00      ( X0 != sK11
% 11.74/2.00      | k1_wellord1(X0,sK10) = k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK9 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2024]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_6924,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK9)
% 11.74/2.00      | sK10 != sK9
% 11.74/2.00      | sK11 != sK11 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_6916]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_15,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_895,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_896,plain,
% 11.74/2.00      ( ~ r2_hidden(X0,k1_wellord1(sK11,X0)) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_895]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_3547,plain,
% 11.74/2.00      ( ~ r2_hidden(sK10,k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_896]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_5,plain,
% 11.74/2.00      ( r1_tarski(X0,X0) ),
% 11.74/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_3227,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1218,plain,( X0 = X0 ),theory(equality) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2741,plain,
% 11.74/2.00      ( sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1218]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2084,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK10,X0),sK11)
% 11.74/2.00      | sK10 = X0 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2678,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 11.74/2.00      | ~ r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
% 11.74/2.00      | sK10 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_2084]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2679,plain,
% 11.74/2.00      ( sK10 = sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
% 11.74/2.00      | r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(k4_tarski(sK10,sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_2678]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1220,plain,
% 11.74/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.74/2.00      theory(equality) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1687,plain,
% 11.74/2.00      ( ~ r1_tarski(X0,X1)
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | k1_wellord1(sK11,sK10) != X1
% 11.74/2.00      | k1_wellord1(sK11,sK9) != X0 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1220]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1958,plain,
% 11.74/2.00      ( ~ r1_tarski(k1_wellord1(sK11,sK9),X0)
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | k1_wellord1(sK11,sK10) != X0
% 11.74/2.00      | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1687]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2530,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10))
% 11.74/2.00      | ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK9))
% 11.74/2.00      | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK9)
% 11.74/2.00      | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1958]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_2100,plain,
% 11.74/2.00      ( sK10 = sK10 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1218]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1959,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK9) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1218]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_8,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 11.74/2.00      | ~ v1_relat_1(X1) ),
% 11.74/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_939,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(X1))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 11.74/2.00      | sK11 != X1 ),
% 11.74/2.00      inference(resolution_lifted,[status(thm)],[c_8,c_38]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_940,plain,
% 11.74/2.00      ( r2_hidden(X0,k3_relat_1(sK11))
% 11.74/2.00      | ~ r2_hidden(k4_tarski(X1,X0),sK11) ),
% 11.74/2.00      inference(unflattening,[status(thm)],[c_939]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1822,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 11.74/2.00      | r2_hidden(sK10,k3_relat_1(sK11)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_940]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1823,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(sK10,k3_relat_1(sK11)) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1822]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1798,plain,
% 11.74/2.00      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
% 11.74/2.00      | r2_hidden(sK9,k3_relat_1(sK11)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_940]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1799,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11) != iProver_top
% 11.74/2.00      | r2_hidden(sK9,k3_relat_1(sK11)) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1750,plain,
% 11.74/2.00      ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK10) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1218]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1726,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_905]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1727,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1707,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11)
% 11.74/2.00      | ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_905]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1708,plain,
% 11.74/2.00      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),sK9),sK11) = iProver_top
% 11.74/2.00      | r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1707]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1679,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1680,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1676,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9))
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1677,plain,
% 11.74/2.00      ( r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK9)) = iProver_top
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_1676]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_1666,plain,
% 11.74/2.00      ( ~ r2_hidden(sK0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)),k1_wellord1(sK11,sK10))
% 11.74/2.00      | r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_426,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_419,plain,
% 11.74/2.00      ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
% 11.74/2.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_3,plain,
% 11.74/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.74/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_129,plain,
% 11.74/2.00      ( ~ r1_tarski(sK11,sK11) | sK11 = sK11 ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(c_125,plain,
% 11.74/2.00      ( r1_tarski(sK11,sK11) ),
% 11.74/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.74/2.00  
% 11.74/2.00  cnf(contradiction,plain,
% 11.74/2.00      ( $false ),
% 11.74/2.00      inference(minisat,
% 11.74/2.00                [status(thm)],
% 11.74/2.00                [c_48985,c_48984,c_43391,c_43080,c_35903,c_33656,c_22864,
% 11.74/2.00                 c_13902,c_7972,c_7968,c_7966,c_7553,c_7547,c_7546,
% 11.74/2.00                 c_6924,c_3547,c_3227,c_2741,c_2679,c_2530,c_2100,c_1959,
% 11.74/2.00                 c_1823,c_1799,c_1750,c_1727,c_1726,c_1708,c_1680,c_1679,
% 11.74/2.00                 c_1677,c_1676,c_1666,c_426,c_425,c_419,c_418,c_129,
% 11.74/2.00                 c_125]) ).
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.74/2.00  
% 11.74/2.00  ------                               Statistics
% 11.74/2.00  
% 11.74/2.00  ------ General
% 11.74/2.00  
% 11.74/2.00  abstr_ref_over_cycles:                  0
% 11.74/2.00  abstr_ref_under_cycles:                 0
% 11.74/2.00  gc_basic_clause_elim:                   0
% 11.74/2.00  forced_gc_time:                         0
% 11.74/2.00  parsing_time:                           0.01
% 11.74/2.00  unif_index_cands_time:                  0.
% 11.74/2.00  unif_index_add_time:                    0.
% 11.74/2.00  orderings_time:                         0.
% 11.74/2.00  out_proof_time:                         0.015
% 11.74/2.00  total_time:                             1.226
% 11.74/2.00  num_of_symbols:                         56
% 11.74/2.00  num_of_terms:                           24020
% 11.74/2.00  
% 11.74/2.00  ------ Preprocessing
% 11.74/2.00  
% 11.74/2.00  num_of_splits:                          0
% 11.74/2.00  num_of_split_atoms:                     0
% 11.74/2.00  num_of_reused_defs:                     0
% 11.74/2.00  num_eq_ax_congr_red:                    30
% 11.74/2.00  num_of_sem_filtered_clauses:            1
% 11.74/2.00  num_of_subtypes:                        0
% 11.74/2.00  monotx_restored_types:                  0
% 11.74/2.00  sat_num_of_epr_types:                   0
% 11.74/2.00  sat_num_of_non_cyclic_types:            0
% 11.74/2.00  sat_guarded_non_collapsed_types:        0
% 11.74/2.00  num_pure_diseq_elim:                    0
% 11.74/2.00  simp_replaced_by:                       0
% 11.74/2.00  res_preprocessed:                       109
% 11.74/2.00  prep_upred:                             0
% 11.74/2.00  prep_unflattend:                        43
% 11.74/2.00  smt_new_axioms:                         0
% 11.74/2.00  pred_elim_cands:                        2
% 11.74/2.00  pred_elim:                              8
% 11.74/2.00  pred_elim_cl:                           20
% 11.74/2.00  pred_elim_cycles:                       13
% 11.74/2.00  merged_defs:                            0
% 11.74/2.00  merged_defs_ncl:                        0
% 11.74/2.00  bin_hyper_res:                          0
% 11.74/2.00  prep_cycles:                            4
% 11.74/2.00  pred_elim_time:                         0.013
% 11.74/2.00  splitting_time:                         0.
% 11.74/2.00  sem_filter_time:                        0.
% 11.74/2.00  monotx_time:                            0.
% 11.74/2.00  subtype_inf_time:                       0.
% 11.74/2.00  
% 11.74/2.00  ------ Problem properties
% 11.74/2.00  
% 11.74/2.00  clauses:                                18
% 11.74/2.00  conjectures:                            0
% 11.74/2.00  epr:                                    3
% 11.74/2.00  horn:                                   12
% 11.74/2.00  ground:                                 2
% 11.74/2.00  unary:                                  4
% 11.74/2.00  binary:                                 5
% 11.74/2.00  lits:                                   44
% 11.74/2.00  lits_eq:                                9
% 11.74/2.00  fd_pure:                                0
% 11.74/2.00  fd_pseudo:                              0
% 11.74/2.00  fd_cond:                                0
% 11.74/2.00  fd_pseudo_cond:                         6
% 11.74/2.00  ac_symbols:                             0
% 11.74/2.00  
% 11.74/2.00  ------ Propositional Solver
% 11.74/2.00  
% 11.74/2.00  prop_solver_calls:                      29
% 11.74/2.00  prop_fast_solver_calls:                 1923
% 11.74/2.00  smt_solver_calls:                       0
% 11.74/2.00  smt_fast_solver_calls:                  0
% 11.74/2.00  prop_num_of_clauses:                    10208
% 11.74/2.00  prop_preprocess_simplified:             19734
% 11.74/2.00  prop_fo_subsumed:                       30
% 11.74/2.00  prop_solver_time:                       0.
% 11.74/2.00  smt_solver_time:                        0.
% 11.74/2.00  smt_fast_solver_time:                   0.
% 11.74/2.00  prop_fast_solver_time:                  0.
% 11.74/2.00  prop_unsat_core_time:                   0.001
% 11.74/2.00  
% 11.74/2.00  ------ QBF
% 11.74/2.00  
% 11.74/2.00  qbf_q_res:                              0
% 11.74/2.00  qbf_num_tautologies:                    0
% 11.74/2.00  qbf_prep_cycles:                        0
% 11.74/2.00  
% 11.74/2.00  ------ BMC1
% 11.74/2.00  
% 11.74/2.00  bmc1_current_bound:                     -1
% 11.74/2.00  bmc1_last_solved_bound:                 -1
% 11.74/2.00  bmc1_unsat_core_size:                   -1
% 11.74/2.00  bmc1_unsat_core_parents_size:           -1
% 11.74/2.00  bmc1_merge_next_fun:                    0
% 11.74/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.74/2.00  
% 11.74/2.00  ------ Instantiation
% 11.74/2.00  
% 11.74/2.00  inst_num_of_clauses:                    2453
% 11.74/2.00  inst_num_in_passive:                    892
% 11.74/2.00  inst_num_in_active:                     1080
% 11.74/2.00  inst_num_in_unprocessed:                481
% 11.74/2.00  inst_num_of_loops:                      1410
% 11.74/2.00  inst_num_of_learning_restarts:          0
% 11.74/2.00  inst_num_moves_active_passive:          328
% 11.74/2.00  inst_lit_activity:                      0
% 11.74/2.00  inst_lit_activity_moves:                0
% 11.74/2.00  inst_num_tautologies:                   0
% 11.74/2.00  inst_num_prop_implied:                  0
% 11.74/2.00  inst_num_existing_simplified:           0
% 11.74/2.00  inst_num_eq_res_simplified:             0
% 11.74/2.00  inst_num_child_elim:                    0
% 11.74/2.00  inst_num_of_dismatching_blockings:      4016
% 11.74/2.00  inst_num_of_non_proper_insts:           3732
% 11.74/2.00  inst_num_of_duplicates:                 0
% 11.74/2.00  inst_inst_num_from_inst_to_res:         0
% 11.74/2.00  inst_dismatching_checking_time:         0.
% 11.74/2.00  
% 11.74/2.00  ------ Resolution
% 11.74/2.00  
% 11.74/2.00  res_num_of_clauses:                     0
% 11.74/2.00  res_num_in_passive:                     0
% 11.74/2.00  res_num_in_active:                      0
% 11.74/2.00  res_num_of_loops:                       113
% 11.74/2.00  res_forward_subset_subsumed:            307
% 11.74/2.00  res_backward_subset_subsumed:           0
% 11.74/2.00  res_forward_subsumed:                   0
% 11.74/2.00  res_backward_subsumed:                  0
% 11.74/2.00  res_forward_subsumption_resolution:     0
% 11.74/2.00  res_backward_subsumption_resolution:    0
% 11.74/2.00  res_clause_to_clause_subsumption:       27125
% 11.74/2.00  res_orphan_elimination:                 0
% 11.74/2.00  res_tautology_del:                      148
% 11.74/2.00  res_num_eq_res_simplified:              0
% 11.74/2.00  res_num_sel_changes:                    0
% 11.74/2.00  res_moves_from_active_to_pass:          0
% 11.74/2.00  
% 11.74/2.00  ------ Superposition
% 11.74/2.00  
% 11.74/2.00  sup_time_total:                         0.
% 11.74/2.00  sup_time_generating:                    0.
% 11.74/2.00  sup_time_sim_full:                      0.
% 11.74/2.00  sup_time_sim_immed:                     0.
% 11.74/2.00  
% 11.74/2.00  sup_num_of_clauses:                     1552
% 11.74/2.00  sup_num_in_active:                      280
% 11.74/2.00  sup_num_in_passive:                     1272
% 11.74/2.00  sup_num_of_loops:                       281
% 11.74/2.00  sup_fw_superposition:                   1936
% 11.74/2.00  sup_bw_superposition:                   2219
% 11.74/2.00  sup_immediate_simplified:               1338
% 11.74/2.00  sup_given_eliminated:                   0
% 11.74/2.00  comparisons_done:                       0
% 11.74/2.00  comparisons_avoided:                    12
% 11.74/2.00  
% 11.74/2.00  ------ Simplifications
% 11.74/2.00  
% 11.74/2.00  
% 11.74/2.00  sim_fw_subset_subsumed:                 469
% 11.74/2.00  sim_bw_subset_subsumed:                 102
% 11.74/2.00  sim_fw_subsumed:                        773
% 11.74/2.00  sim_bw_subsumed:                        6
% 11.74/2.00  sim_fw_subsumption_res:                 11
% 11.74/2.00  sim_bw_subsumption_res:                 0
% 11.74/2.00  sim_tautology_del:                      66
% 11.74/2.00  sim_eq_tautology_del:                   71
% 11.74/2.00  sim_eq_res_simp:                        10
% 11.74/2.00  sim_fw_demodulated:                     0
% 11.74/2.00  sim_bw_demodulated:                     0
% 11.74/2.00  sim_light_normalised:                   0
% 11.74/2.00  sim_joinable_taut:                      0
% 11.74/2.00  sim_joinable_simp:                      0
% 11.74/2.00  sim_ac_normalised:                      0
% 11.74/2.00  sim_smt_subsumption:                    0
% 11.74/2.00  
%------------------------------------------------------------------------------
