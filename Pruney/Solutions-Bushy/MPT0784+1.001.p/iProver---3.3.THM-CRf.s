%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  212 (1973 expanded)
%              Number of clauses        :  137 ( 583 expanded)
%              Number of leaves         :   21 ( 388 expanded)
%              Depth                    :   22
%              Number of atoms          :  826 (8840 expanded)
%              Number of equality atoms :  255 (1382 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

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
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f88,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f21])).

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

fof(f79,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f18])).

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

fof(f71,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f8])).

fof(f85,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

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

fof(f75,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord1(X1,X0) = k1_xboole_0
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k1_xboole_0
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f94,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f93])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1699,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1099,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_37])).

cnf(c_1100,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X1))
    | r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(unflattening,[status(thm)],[c_1099])).

cnf(c_1685,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_2425,plain,
    ( r1_tarski(k1_wellord1(sK11,X0),X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,X0),X1),X0),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1685])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1066,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_1067,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v6_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1066])).

cnf(c_11,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,negated_conjecture,
    ( v2_wellord1(sK11) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_440,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_441,plain,
    ( v6_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_105,plain,
    ( v6_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_443,plain,
    ( v6_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_37,c_36,c_105])).

cnf(c_917,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_443])).

cnf(c_918,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_37])).

cnf(c_923,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_1070,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | ~ r2_hidden(X0,k3_relat_1(sK11))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_37,c_918])).

cnf(c_1071,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | ~ r2_hidden(X1,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X1,X0),sK11)
    | r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_1070])).

cnf(c_1691,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_21,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1139,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v8_relat_2(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_1140,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v8_relat_2(sK11) ),
    inference(unflattening,[status(thm)],[c_1139])).

cnf(c_13,plain,
    ( v8_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_418,plain,
    ( v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_419,plain,
    ( v8_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_99,plain,
    ( v8_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_421,plain,
    ( v8_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_37,c_36,c_99])).

cnf(c_747,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X2)
    | r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_421])).

cnf(c_748,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_750,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_37])).

cnf(c_751,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_750])).

cnf(c_1142,plain,
    ( r2_hidden(k4_tarski(X2,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1140,c_37,c_748])).

cnf(c_1143,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X2,X0),sK11)
    | r2_hidden(k4_tarski(X2,X1),sK11) ),
    inference(renaming,[status(thm)],[c_1142])).

cnf(c_1692,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top
    | r2_hidden(k4_tarski(X2,X1),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_2768,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK11) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top
    | r2_hidden(k4_tarski(X2,X1),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1692])).

cnf(c_4682,plain,
    ( X0 = X1
    | r1_tarski(k1_wellord1(sK11,X1),X2) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,X1),X2),X0),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2425,c_2768])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1109,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_37])).

cnf(c_1110,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_1684,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_16833,plain,
    ( X0 = X1
    | sK1(k1_wellord1(sK11,X0),X2) = X1
    | r1_tarski(k1_wellord1(sK11,X0),X2) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK1(k1_wellord1(sK11,X0),X2),k1_wellord1(sK11,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_4682,c_1684])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1700,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17251,plain,
    ( X0 = X1
    | sK1(k1_wellord1(sK11,X1),k1_wellord1(sK11,X0)) = X0
    | r1_tarski(k1_wellord1(sK11,X1),k1_wellord1(sK11,X0)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_16833,c_1700])).

cnf(c_16,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,negated_conjecture,
    ( ~ r3_xboole_0(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_468,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X1
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_469,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1695,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_18573,plain,
    ( sK1(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10
    | sK10 = sK9
    | r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17251,c_1695])).

cnf(c_32,plain,
    ( r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_482,plain,
    ( k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_483,plain,
    ( k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK10) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_15,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_475,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_476,plain,
    ( ~ r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_546,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_476])).

cnf(c_547,plain,
    ( r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_548,plain,
    ( r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_34,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_560,plain,
    ( k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_469])).

cnf(c_561,plain,
    ( k1_wellord1(sK11,sK9) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( k1_wellord1(sK11,sK10) != k1_xboole_0
    | k1_wellord1(sK11,sK9) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_476])).

cnf(c_566,plain,
    ( k1_wellord1(sK11,sK10) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_1403,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1418,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1405,plain,
    ( X0 != X1
    | X2 != X3
    | k1_wellord1(X0,X2) = k1_wellord1(X1,X3) ),
    theory(equality)).

cnf(c_1754,plain,
    ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10)
    | sK9 != sK10
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1807,plain,
    ( ~ r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_1808,plain,
    ( r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_1811,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
    | r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | sK9 = sK10 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1812,plain,
    ( sK9 = sK10
    | r2_hidden(k4_tarski(sK10,sK9),sK11) != iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_25,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1122,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_1123,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v4_relat_2(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_1122])).

cnf(c_12,plain,
    ( v4_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_429,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_430,plain,
    ( v4_relat_2(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_102,plain,
    ( v4_relat_2(sK11)
    | ~ v2_wellord1(sK11)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_432,plain,
    ( v4_relat_2(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_37,c_36,c_102])).

cnf(c_651,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_432])).

cnf(c_652,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_1125,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1123,c_37,c_652])).

cnf(c_1126,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),sK11)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1125])).

cnf(c_1810,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(k4_tarski(sK9,sK10),sK11)
    | sK9 = sK10 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1814,plain,
    ( sK9 = sK10
    | r2_hidden(k4_tarski(sK10,sK9),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK10),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_33,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_wellord1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1054,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | k1_wellord1(X1,X0) = k1_xboole_0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_1055,plain,
    ( r2_hidden(X0,k3_relat_1(sK11))
    | k1_wellord1(sK11,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_1833,plain,
    ( r2_hidden(sK10,k3_relat_1(sK11))
    | k1_wellord1(sK11,sK10) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1834,plain,
    ( k1_wellord1(sK11,sK10) = k1_xboole_0
    | r2_hidden(sK10,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_2098,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_2190,plain,
    ( r2_hidden(sK9,k3_relat_1(sK11))
    | k1_wellord1(sK11,sK9) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_2193,plain,
    ( k1_wellord1(sK11,sK9) = k1_xboole_0
    | r2_hidden(sK9,k3_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_2573,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_2574,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK11) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2573])).

cnf(c_2796,plain,
    ( k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_2074,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK10,X0),sK11)
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_2928,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11)
    | ~ r2_hidden(k4_tarski(sK10,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | sK10 = sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_2929,plain,
    ( sK10 = sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
    | r2_hidden(k4_tarski(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),sK10),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2928])).

cnf(c_1408,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1760,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(sK11,X2))
    | X2 != X0
    | k1_wellord1(sK11,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_1936,plain,
    ( r2_hidden(X0,k1_wellord1(sK11,X0))
    | ~ r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | X0 != sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,X0) != k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_3167,plain,
    ( ~ r2_hidden(sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)),k1_wellord1(sK11,sK10))
    | r2_hidden(sK10,k1_wellord1(sK11,sK10))
    | k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK10)
    | sK10 != sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1090,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_1091,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK11,X0)) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_3374,plain,
    ( ~ r2_hidden(sK10,k1_wellord1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_3134,plain,
    ( X0 != sK9
    | k1_wellord1(sK11,X0) = k1_wellord1(sK11,sK9)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_4302,plain,
    ( k1_wellord1(sK11,sK10) = k1_wellord1(sK11,sK9)
    | sK10 != sK9
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_1404,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1752,plain,
    ( k1_wellord1(sK11,sK10) != X0
    | k1_wellord1(sK11,sK9) != X0
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1838,plain,
    ( k1_wellord1(sK11,sK10) != k1_wellord1(X0,X1)
    | k1_wellord1(sK11,sK9) != k1_wellord1(X0,X1)
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_4305,plain,
    ( k1_wellord1(sK11,sK10) != k1_wellord1(sK11,sK9)
    | k1_wellord1(sK11,sK9) = k1_wellord1(sK11,sK10)
    | k1_wellord1(sK11,sK9) != k1_wellord1(sK11,sK9) ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_2084,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,sK10),sK11)
    | r2_hidden(k4_tarski(sK10,X0),sK11)
    | ~ r2_hidden(sK10,k3_relat_1(sK11))
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_4845,plain,
    ( r2_hidden(k4_tarski(sK10,sK10),sK11)
    | ~ r2_hidden(sK10,k3_relat_1(sK11))
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_3732,plain,
    ( r2_hidden(k4_tarski(sK10,X0),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,X0)) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_7255,plain,
    ( r2_hidden(k4_tarski(sK10,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) ),
    inference(instantiation,[status(thm)],[c_3732])).

cnf(c_7257,plain,
    ( r2_hidden(k4_tarski(sK10,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))),sK11) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7255])).

cnf(c_4699,plain,
    ( ~ r2_hidden(k4_tarski(sK10,X0),sK11)
    | r2_hidden(sK10,k1_wellord1(sK11,X0))
    | X0 = sK10 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_8072,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK10),sK11)
    | r2_hidden(sK10,k1_wellord1(sK11,sK10))
    | sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_4699])).

cnf(c_8699,plain,
    ( sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != sK9
    | k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) = k1_wellord1(sK11,sK9)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_2563,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | X1 != k1_wellord1(sK11,sK9)
    | X0 != sK10 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_8424,plain,
    ( r2_hidden(sK10,X0)
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | X0 != k1_wellord1(sK11,sK9)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_2563])).

cnf(c_17997,plain,
    ( r2_hidden(sK10,k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))))
    | ~ r2_hidden(sK10,k1_wellord1(sK11,sK9))
    | k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_8424])).

cnf(c_17998,plain,
    ( k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9))) != k1_wellord1(sK11,sK9)
    | sK10 != sK10
    | r2_hidden(sK10,k1_wellord1(sK11,sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)))) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17997])).

cnf(c_1694,plain,
    ( r1_tarski(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_18574,plain,
    ( sK1(k1_wellord1(sK11,sK10),k1_wellord1(sK11,sK9)) = sK9
    | sK10 = sK9
    | r2_hidden(k4_tarski(sK9,sK10),sK11) = iProver_top
    | r2_hidden(sK10,k3_relat_1(sK11)) != iProver_top
    | r2_hidden(sK9,k3_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17251,c_1694])).

cnf(c_19000,plain,
    ( sK1(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18573,c_483,c_547,c_548,c_561,c_566,c_1418,c_1754,c_1808,c_1812,c_1814,c_1833,c_1834,c_2098,c_2193,c_2574,c_2796,c_2929,c_3167,c_3374,c_4302,c_4305,c_4845,c_7257,c_8072,c_8699,c_17998,c_18574])).

cnf(c_19004,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) = iProver_top
    | r2_hidden(sK10,k1_wellord1(sK11,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19000,c_1699])).

cnf(c_470,plain,
    ( r1_tarski(k1_wellord1(sK11,sK9),k1_wellord1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19004,c_18574,c_17998,c_8699,c_8072,c_7257,c_4845,c_4305,c_4302,c_3374,c_3167,c_2929,c_2796,c_2574,c_2193,c_2098,c_1834,c_1833,c_1814,c_1808,c_1754,c_1418,c_566,c_561,c_548,c_547,c_483,c_470])).


%------------------------------------------------------------------------------
