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
% DateTime   : Thu Dec  3 11:54:33 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 220 expanded)
%              Number of clauses        :   43 (  64 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  447 (1467 expanded)
%              Number of equality atoms :  105 ( 238 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
        & sK1(X0) != sK2(X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0))
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
            & sK1(X0) != sK2(X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0))
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).

fof(f46,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        & ! [X3] :
            ( ( X1 != X3
              & r2_hidden(k4_tarski(X3,X1),X2) )
            | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5)
      & ! [X3] :
          ( ( sK4 != X3
            & r2_hidden(k4_tarski(X3,sK4),sK5) )
          | ~ r2_hidden(X3,k1_wellord1(sK5,sK3)) )
      & r2_hidden(sK4,k3_relat_1(sK5))
      & r2_hidden(sK3,k3_relat_1(sK5))
      & v2_wellord1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5)
    & ! [X3] :
        ( ( sK4 != X3
          & r2_hidden(k4_tarski(X3,sK4),sK5) )
        | ~ r2_hidden(X3,k1_wellord1(sK5,sK3)) )
    & r2_hidden(sK4,k3_relat_1(sK5))
    & r2_hidden(sK3,k3_relat_1(sK5))
    & v2_wellord1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f29])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    v2_wellord1(sK5) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f9,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ~ r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    r2_hidden(sK3,k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    r2_hidden(sK4,k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X3] :
      ( sK4 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK5,sK3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ~ r2_hidden(sK4,k1_wellord1(sK5,sK3)) ),
    inference(equality_resolution,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ v6_relat_2(sK5)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_28,negated_conjecture,
    ( v2_wellord1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_73,plain,
    ( v6_relat_2(sK5)
    | ~ v2_wellord1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_457,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | ~ r2_hidden(X0,k3_relat_1(sK5))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_29,c_28,c_73])).

cnf(c_458,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | r2_hidden(k4_tarski(X1,X0),sK5)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_922,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_relat_1(sK5)) != iProver_top
    | r2_hidden(X1,k3_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_932,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1711,plain,
    ( sK4 = sK3
    | r2_hidden(k4_tarski(sK4,sK3),sK5) = iProver_top
    | r2_hidden(sK4,k3_relat_1(sK5)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_932])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_wellord1(sK5,sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_649,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1103,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_498,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_499,plain,
    ( r2_hidden(X0,k1_wellord1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1095,plain,
    ( ~ r2_hidden(k4_tarski(sK4,X0),sK5)
    | r2_hidden(sK4,k1_wellord1(sK5,X0))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_1396,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK3),sK5)
    | r2_hidden(sK4,k1_wellord1(sK5,sK3))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1756,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK5)
    | ~ r2_hidden(sK4,k3_relat_1(sK5))
    | ~ r2_hidden(sK3,k3_relat_1(sK5))
    | sK4 = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1711])).

cnf(c_650,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1143,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_1424,plain,
    ( X0 != sK4
    | X0 = sK3
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_1795,plain,
    ( sK4 != sK4
    | sK4 = sK3
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1955,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1711,c_27,c_26,c_24,c_1103,c_1396,c_1756,c_1795])).

cnf(c_1960,plain,
    ( r2_hidden(k4_tarski(sK3,sK3),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1955,c_932])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1404,plain,
    ( r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1405,plain,
    ( r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X0))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1))
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | ~ r2_hidden(X0,k3_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_29])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(X1,k3_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_1062,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK5))
    | r2_hidden(k4_tarski(sK3,X0),sK5)
    | ~ r2_hidden(sK3,k3_relat_1(sK5))
    | ~ r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1205,plain,
    ( r2_hidden(k4_tarski(sK3,sK3),sK5)
    | ~ r2_hidden(sK3,k3_relat_1(sK5))
    | ~ r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1206,plain,
    ( r2_hidden(k4_tarski(sK3,sK3),sK5) = iProver_top
    | r2_hidden(sK3,k3_relat_1(sK5)) != iProver_top
    | r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_32,plain,
    ( r2_hidden(sK3,k3_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1960,c_1405,c_1206,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.56/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.56/1.00  
% 1.56/1.00  ------  iProver source info
% 1.56/1.00  
% 1.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.56/1.00  git: non_committed_changes: false
% 1.56/1.00  git: last_make_outside_of_git: false
% 1.56/1.00  
% 1.56/1.00  ------ 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options
% 1.56/1.00  
% 1.56/1.00  --out_options                           all
% 1.56/1.00  --tptp_safe_out                         true
% 1.56/1.00  --problem_path                          ""
% 1.56/1.00  --include_path                          ""
% 1.56/1.00  --clausifier                            res/vclausify_rel
% 1.56/1.00  --clausifier_options                    --mode clausify
% 1.56/1.00  --stdin                                 false
% 1.56/1.00  --stats_out                             all
% 1.56/1.00  
% 1.56/1.00  ------ General Options
% 1.56/1.00  
% 1.56/1.00  --fof                                   false
% 1.56/1.00  --time_out_real                         305.
% 1.56/1.00  --time_out_virtual                      -1.
% 1.56/1.00  --symbol_type_check                     false
% 1.56/1.00  --clausify_out                          false
% 1.56/1.00  --sig_cnt_out                           false
% 1.56/1.00  --trig_cnt_out                          false
% 1.56/1.00  --trig_cnt_out_tolerance                1.
% 1.56/1.00  --trig_cnt_out_sk_spl                   false
% 1.56/1.00  --abstr_cl_out                          false
% 1.56/1.00  
% 1.56/1.00  ------ Global Options
% 1.56/1.00  
% 1.56/1.00  --schedule                              default
% 1.56/1.00  --add_important_lit                     false
% 1.56/1.00  --prop_solver_per_cl                    1000
% 1.56/1.00  --min_unsat_core                        false
% 1.56/1.00  --soft_assumptions                      false
% 1.56/1.00  --soft_lemma_size                       3
% 1.56/1.00  --prop_impl_unit_size                   0
% 1.56/1.00  --prop_impl_unit                        []
% 1.56/1.00  --share_sel_clauses                     true
% 1.56/1.00  --reset_solvers                         false
% 1.56/1.00  --bc_imp_inh                            [conj_cone]
% 1.56/1.00  --conj_cone_tolerance                   3.
% 1.56/1.00  --extra_neg_conj                        none
% 1.56/1.00  --large_theory_mode                     true
% 1.56/1.00  --prolific_symb_bound                   200
% 1.56/1.00  --lt_threshold                          2000
% 1.56/1.00  --clause_weak_htbl                      true
% 1.56/1.00  --gc_record_bc_elim                     false
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing Options
% 1.56/1.00  
% 1.56/1.00  --preprocessing_flag                    true
% 1.56/1.00  --time_out_prep_mult                    0.1
% 1.56/1.00  --splitting_mode                        input
% 1.56/1.00  --splitting_grd                         true
% 1.56/1.00  --splitting_cvd                         false
% 1.56/1.00  --splitting_cvd_svl                     false
% 1.56/1.00  --splitting_nvd                         32
% 1.56/1.00  --sub_typing                            true
% 1.56/1.00  --prep_gs_sim                           true
% 1.56/1.00  --prep_unflatten                        true
% 1.56/1.00  --prep_res_sim                          true
% 1.56/1.00  --prep_upred                            true
% 1.56/1.00  --prep_sem_filter                       exhaustive
% 1.56/1.00  --prep_sem_filter_out                   false
% 1.56/1.00  --pred_elim                             true
% 1.56/1.00  --res_sim_input                         true
% 1.56/1.00  --eq_ax_congr_red                       true
% 1.56/1.00  --pure_diseq_elim                       true
% 1.56/1.00  --brand_transform                       false
% 1.56/1.00  --non_eq_to_eq                          false
% 1.56/1.00  --prep_def_merge                        true
% 1.56/1.00  --prep_def_merge_prop_impl              false
% 1.56/1.00  --prep_def_merge_mbd                    true
% 1.56/1.00  --prep_def_merge_tr_red                 false
% 1.56/1.00  --prep_def_merge_tr_cl                  false
% 1.56/1.00  --smt_preprocessing                     true
% 1.56/1.00  --smt_ac_axioms                         fast
% 1.56/1.00  --preprocessed_out                      false
% 1.56/1.00  --preprocessed_stats                    false
% 1.56/1.00  
% 1.56/1.00  ------ Abstraction refinement Options
% 1.56/1.00  
% 1.56/1.00  --abstr_ref                             []
% 1.56/1.00  --abstr_ref_prep                        false
% 1.56/1.00  --abstr_ref_until_sat                   false
% 1.56/1.00  --abstr_ref_sig_restrict                funpre
% 1.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/1.00  --abstr_ref_under                       []
% 1.56/1.00  
% 1.56/1.00  ------ SAT Options
% 1.56/1.00  
% 1.56/1.00  --sat_mode                              false
% 1.56/1.00  --sat_fm_restart_options                ""
% 1.56/1.00  --sat_gr_def                            false
% 1.56/1.00  --sat_epr_types                         true
% 1.56/1.00  --sat_non_cyclic_types                  false
% 1.56/1.00  --sat_finite_models                     false
% 1.56/1.00  --sat_fm_lemmas                         false
% 1.56/1.00  --sat_fm_prep                           false
% 1.56/1.00  --sat_fm_uc_incr                        true
% 1.56/1.00  --sat_out_model                         small
% 1.56/1.00  --sat_out_clauses                       false
% 1.56/1.00  
% 1.56/1.00  ------ QBF Options
% 1.56/1.00  
% 1.56/1.00  --qbf_mode                              false
% 1.56/1.00  --qbf_elim_univ                         false
% 1.56/1.00  --qbf_dom_inst                          none
% 1.56/1.00  --qbf_dom_pre_inst                      false
% 1.56/1.00  --qbf_sk_in                             false
% 1.56/1.00  --qbf_pred_elim                         true
% 1.56/1.00  --qbf_split                             512
% 1.56/1.00  
% 1.56/1.00  ------ BMC1 Options
% 1.56/1.00  
% 1.56/1.00  --bmc1_incremental                      false
% 1.56/1.00  --bmc1_axioms                           reachable_all
% 1.56/1.00  --bmc1_min_bound                        0
% 1.56/1.00  --bmc1_max_bound                        -1
% 1.56/1.00  --bmc1_max_bound_default                -1
% 1.56/1.00  --bmc1_symbol_reachability              true
% 1.56/1.00  --bmc1_property_lemmas                  false
% 1.56/1.00  --bmc1_k_induction                      false
% 1.56/1.00  --bmc1_non_equiv_states                 false
% 1.56/1.00  --bmc1_deadlock                         false
% 1.56/1.00  --bmc1_ucm                              false
% 1.56/1.00  --bmc1_add_unsat_core                   none
% 1.56/1.00  --bmc1_unsat_core_children              false
% 1.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/1.00  --bmc1_out_stat                         full
% 1.56/1.00  --bmc1_ground_init                      false
% 1.56/1.00  --bmc1_pre_inst_next_state              false
% 1.56/1.00  --bmc1_pre_inst_state                   false
% 1.56/1.00  --bmc1_pre_inst_reach_state             false
% 1.56/1.00  --bmc1_out_unsat_core                   false
% 1.56/1.00  --bmc1_aig_witness_out                  false
% 1.56/1.00  --bmc1_verbose                          false
% 1.56/1.00  --bmc1_dump_clauses_tptp                false
% 1.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.56/1.00  --bmc1_dump_file                        -
% 1.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.56/1.00  --bmc1_ucm_extend_mode                  1
% 1.56/1.00  --bmc1_ucm_init_mode                    2
% 1.56/1.00  --bmc1_ucm_cone_mode                    none
% 1.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.56/1.00  --bmc1_ucm_relax_model                  4
% 1.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/1.00  --bmc1_ucm_layered_model                none
% 1.56/1.00  --bmc1_ucm_max_lemma_size               10
% 1.56/1.00  
% 1.56/1.00  ------ AIG Options
% 1.56/1.00  
% 1.56/1.00  --aig_mode                              false
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation Options
% 1.56/1.00  
% 1.56/1.00  --instantiation_flag                    true
% 1.56/1.00  --inst_sos_flag                         false
% 1.56/1.00  --inst_sos_phase                        true
% 1.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel_side                     num_symb
% 1.56/1.00  --inst_solver_per_active                1400
% 1.56/1.00  --inst_solver_calls_frac                1.
% 1.56/1.00  --inst_passive_queue_type               priority_queues
% 1.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/1.00  --inst_passive_queues_freq              [25;2]
% 1.56/1.00  --inst_dismatching                      true
% 1.56/1.00  --inst_eager_unprocessed_to_passive     true
% 1.56/1.00  --inst_prop_sim_given                   true
% 1.56/1.00  --inst_prop_sim_new                     false
% 1.56/1.00  --inst_subs_new                         false
% 1.56/1.00  --inst_eq_res_simp                      false
% 1.56/1.00  --inst_subs_given                       false
% 1.56/1.00  --inst_orphan_elimination               true
% 1.56/1.00  --inst_learning_loop_flag               true
% 1.56/1.00  --inst_learning_start                   3000
% 1.56/1.00  --inst_learning_factor                  2
% 1.56/1.00  --inst_start_prop_sim_after_learn       3
% 1.56/1.00  --inst_sel_renew                        solver
% 1.56/1.00  --inst_lit_activity_flag                true
% 1.56/1.00  --inst_restr_to_given                   false
% 1.56/1.00  --inst_activity_threshold               500
% 1.56/1.00  --inst_out_proof                        true
% 1.56/1.00  
% 1.56/1.00  ------ Resolution Options
% 1.56/1.00  
% 1.56/1.00  --resolution_flag                       true
% 1.56/1.00  --res_lit_sel                           adaptive
% 1.56/1.00  --res_lit_sel_side                      none
% 1.56/1.00  --res_ordering                          kbo
% 1.56/1.00  --res_to_prop_solver                    active
% 1.56/1.00  --res_prop_simpl_new                    false
% 1.56/1.00  --res_prop_simpl_given                  true
% 1.56/1.00  --res_passive_queue_type                priority_queues
% 1.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/1.00  --res_passive_queues_freq               [15;5]
% 1.56/1.00  --res_forward_subs                      full
% 1.56/1.00  --res_backward_subs                     full
% 1.56/1.00  --res_forward_subs_resolution           true
% 1.56/1.00  --res_backward_subs_resolution          true
% 1.56/1.00  --res_orphan_elimination                true
% 1.56/1.00  --res_time_limit                        2.
% 1.56/1.00  --res_out_proof                         true
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Options
% 1.56/1.00  
% 1.56/1.00  --superposition_flag                    true
% 1.56/1.00  --sup_passive_queue_type                priority_queues
% 1.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.56/1.00  --demod_completeness_check              fast
% 1.56/1.00  --demod_use_ground                      true
% 1.56/1.00  --sup_to_prop_solver                    passive
% 1.56/1.00  --sup_prop_simpl_new                    true
% 1.56/1.00  --sup_prop_simpl_given                  true
% 1.56/1.00  --sup_fun_splitting                     false
% 1.56/1.00  --sup_smt_interval                      50000
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Simplification Setup
% 1.56/1.00  
% 1.56/1.00  --sup_indices_passive                   []
% 1.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_full_bw                           [BwDemod]
% 1.56/1.00  --sup_immed_triv                        [TrivRules]
% 1.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_immed_bw_main                     []
% 1.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  
% 1.56/1.00  ------ Combination Options
% 1.56/1.00  
% 1.56/1.00  --comb_res_mult                         3
% 1.56/1.00  --comb_sup_mult                         2
% 1.56/1.00  --comb_inst_mult                        10
% 1.56/1.00  
% 1.56/1.00  ------ Debug Options
% 1.56/1.00  
% 1.56/1.00  --dbg_backtrace                         false
% 1.56/1.00  --dbg_dump_prop_clauses                 false
% 1.56/1.00  --dbg_dump_prop_clauses_file            -
% 1.56/1.00  --dbg_out_stat                          false
% 1.56/1.00  ------ Parsing...
% 1.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.56/1.00  ------ Proving...
% 1.56/1.00  ------ Problem Properties 
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  clauses                                 16
% 1.56/1.00  conjectures                             5
% 1.56/1.00  EPR                                     2
% 1.56/1.00  Horn                                    11
% 1.56/1.00  unary                                   6
% 1.56/1.00  binary                                  2
% 1.56/1.00  lits                                    39
% 1.56/1.00  lits eq                                 8
% 1.56/1.00  fd_pure                                 0
% 1.56/1.00  fd_pseudo                               0
% 1.56/1.00  fd_cond                                 0
% 1.56/1.00  fd_pseudo_cond                          5
% 1.56/1.00  AC symbols                              0
% 1.56/1.00  
% 1.56/1.00  ------ Schedule dynamic 5 is on 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  ------ 
% 1.56/1.00  Current options:
% 1.56/1.00  ------ 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options
% 1.56/1.00  
% 1.56/1.00  --out_options                           all
% 1.56/1.00  --tptp_safe_out                         true
% 1.56/1.00  --problem_path                          ""
% 1.56/1.00  --include_path                          ""
% 1.56/1.00  --clausifier                            res/vclausify_rel
% 1.56/1.00  --clausifier_options                    --mode clausify
% 1.56/1.00  --stdin                                 false
% 1.56/1.00  --stats_out                             all
% 1.56/1.00  
% 1.56/1.00  ------ General Options
% 1.56/1.00  
% 1.56/1.00  --fof                                   false
% 1.56/1.00  --time_out_real                         305.
% 1.56/1.00  --time_out_virtual                      -1.
% 1.56/1.00  --symbol_type_check                     false
% 1.56/1.00  --clausify_out                          false
% 1.56/1.00  --sig_cnt_out                           false
% 1.56/1.00  --trig_cnt_out                          false
% 1.56/1.00  --trig_cnt_out_tolerance                1.
% 1.56/1.00  --trig_cnt_out_sk_spl                   false
% 1.56/1.00  --abstr_cl_out                          false
% 1.56/1.00  
% 1.56/1.00  ------ Global Options
% 1.56/1.00  
% 1.56/1.00  --schedule                              default
% 1.56/1.00  --add_important_lit                     false
% 1.56/1.00  --prop_solver_per_cl                    1000
% 1.56/1.00  --min_unsat_core                        false
% 1.56/1.00  --soft_assumptions                      false
% 1.56/1.00  --soft_lemma_size                       3
% 1.56/1.00  --prop_impl_unit_size                   0
% 1.56/1.00  --prop_impl_unit                        []
% 1.56/1.00  --share_sel_clauses                     true
% 1.56/1.00  --reset_solvers                         false
% 1.56/1.00  --bc_imp_inh                            [conj_cone]
% 1.56/1.00  --conj_cone_tolerance                   3.
% 1.56/1.00  --extra_neg_conj                        none
% 1.56/1.00  --large_theory_mode                     true
% 1.56/1.00  --prolific_symb_bound                   200
% 1.56/1.00  --lt_threshold                          2000
% 1.56/1.00  --clause_weak_htbl                      true
% 1.56/1.00  --gc_record_bc_elim                     false
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing Options
% 1.56/1.00  
% 1.56/1.00  --preprocessing_flag                    true
% 1.56/1.00  --time_out_prep_mult                    0.1
% 1.56/1.00  --splitting_mode                        input
% 1.56/1.00  --splitting_grd                         true
% 1.56/1.00  --splitting_cvd                         false
% 1.56/1.00  --splitting_cvd_svl                     false
% 1.56/1.00  --splitting_nvd                         32
% 1.56/1.00  --sub_typing                            true
% 1.56/1.00  --prep_gs_sim                           true
% 1.56/1.00  --prep_unflatten                        true
% 1.56/1.00  --prep_res_sim                          true
% 1.56/1.00  --prep_upred                            true
% 1.56/1.00  --prep_sem_filter                       exhaustive
% 1.56/1.00  --prep_sem_filter_out                   false
% 1.56/1.00  --pred_elim                             true
% 1.56/1.00  --res_sim_input                         true
% 1.56/1.00  --eq_ax_congr_red                       true
% 1.56/1.00  --pure_diseq_elim                       true
% 1.56/1.00  --brand_transform                       false
% 1.56/1.00  --non_eq_to_eq                          false
% 1.56/1.00  --prep_def_merge                        true
% 1.56/1.00  --prep_def_merge_prop_impl              false
% 1.56/1.00  --prep_def_merge_mbd                    true
% 1.56/1.00  --prep_def_merge_tr_red                 false
% 1.56/1.00  --prep_def_merge_tr_cl                  false
% 1.56/1.00  --smt_preprocessing                     true
% 1.56/1.00  --smt_ac_axioms                         fast
% 1.56/1.00  --preprocessed_out                      false
% 1.56/1.00  --preprocessed_stats                    false
% 1.56/1.00  
% 1.56/1.00  ------ Abstraction refinement Options
% 1.56/1.00  
% 1.56/1.00  --abstr_ref                             []
% 1.56/1.00  --abstr_ref_prep                        false
% 1.56/1.00  --abstr_ref_until_sat                   false
% 1.56/1.00  --abstr_ref_sig_restrict                funpre
% 1.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/1.00  --abstr_ref_under                       []
% 1.56/1.00  
% 1.56/1.00  ------ SAT Options
% 1.56/1.00  
% 1.56/1.00  --sat_mode                              false
% 1.56/1.00  --sat_fm_restart_options                ""
% 1.56/1.00  --sat_gr_def                            false
% 1.56/1.00  --sat_epr_types                         true
% 1.56/1.00  --sat_non_cyclic_types                  false
% 1.56/1.00  --sat_finite_models                     false
% 1.56/1.00  --sat_fm_lemmas                         false
% 1.56/1.00  --sat_fm_prep                           false
% 1.56/1.00  --sat_fm_uc_incr                        true
% 1.56/1.00  --sat_out_model                         small
% 1.56/1.00  --sat_out_clauses                       false
% 1.56/1.00  
% 1.56/1.00  ------ QBF Options
% 1.56/1.00  
% 1.56/1.00  --qbf_mode                              false
% 1.56/1.00  --qbf_elim_univ                         false
% 1.56/1.00  --qbf_dom_inst                          none
% 1.56/1.00  --qbf_dom_pre_inst                      false
% 1.56/1.00  --qbf_sk_in                             false
% 1.56/1.00  --qbf_pred_elim                         true
% 1.56/1.00  --qbf_split                             512
% 1.56/1.00  
% 1.56/1.00  ------ BMC1 Options
% 1.56/1.00  
% 1.56/1.00  --bmc1_incremental                      false
% 1.56/1.00  --bmc1_axioms                           reachable_all
% 1.56/1.00  --bmc1_min_bound                        0
% 1.56/1.00  --bmc1_max_bound                        -1
% 1.56/1.00  --bmc1_max_bound_default                -1
% 1.56/1.00  --bmc1_symbol_reachability              true
% 1.56/1.00  --bmc1_property_lemmas                  false
% 1.56/1.00  --bmc1_k_induction                      false
% 1.56/1.00  --bmc1_non_equiv_states                 false
% 1.56/1.00  --bmc1_deadlock                         false
% 1.56/1.00  --bmc1_ucm                              false
% 1.56/1.00  --bmc1_add_unsat_core                   none
% 1.56/1.00  --bmc1_unsat_core_children              false
% 1.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/1.00  --bmc1_out_stat                         full
% 1.56/1.00  --bmc1_ground_init                      false
% 1.56/1.00  --bmc1_pre_inst_next_state              false
% 1.56/1.00  --bmc1_pre_inst_state                   false
% 1.56/1.00  --bmc1_pre_inst_reach_state             false
% 1.56/1.00  --bmc1_out_unsat_core                   false
% 1.56/1.00  --bmc1_aig_witness_out                  false
% 1.56/1.00  --bmc1_verbose                          false
% 1.56/1.00  --bmc1_dump_clauses_tptp                false
% 1.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.56/1.00  --bmc1_dump_file                        -
% 1.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.56/1.00  --bmc1_ucm_extend_mode                  1
% 1.56/1.00  --bmc1_ucm_init_mode                    2
% 1.56/1.00  --bmc1_ucm_cone_mode                    none
% 1.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.56/1.00  --bmc1_ucm_relax_model                  4
% 1.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/1.00  --bmc1_ucm_layered_model                none
% 1.56/1.00  --bmc1_ucm_max_lemma_size               10
% 1.56/1.00  
% 1.56/1.00  ------ AIG Options
% 1.56/1.00  
% 1.56/1.00  --aig_mode                              false
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation Options
% 1.56/1.00  
% 1.56/1.00  --instantiation_flag                    true
% 1.56/1.00  --inst_sos_flag                         false
% 1.56/1.00  --inst_sos_phase                        true
% 1.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel_side                     none
% 1.56/1.00  --inst_solver_per_active                1400
% 1.56/1.00  --inst_solver_calls_frac                1.
% 1.56/1.00  --inst_passive_queue_type               priority_queues
% 1.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/1.00  --inst_passive_queues_freq              [25;2]
% 1.56/1.00  --inst_dismatching                      true
% 1.56/1.00  --inst_eager_unprocessed_to_passive     true
% 1.56/1.00  --inst_prop_sim_given                   true
% 1.56/1.00  --inst_prop_sim_new                     false
% 1.56/1.00  --inst_subs_new                         false
% 1.56/1.00  --inst_eq_res_simp                      false
% 1.56/1.00  --inst_subs_given                       false
% 1.56/1.00  --inst_orphan_elimination               true
% 1.56/1.00  --inst_learning_loop_flag               true
% 1.56/1.00  --inst_learning_start                   3000
% 1.56/1.00  --inst_learning_factor                  2
% 1.56/1.00  --inst_start_prop_sim_after_learn       3
% 1.56/1.00  --inst_sel_renew                        solver
% 1.56/1.00  --inst_lit_activity_flag                true
% 1.56/1.00  --inst_restr_to_given                   false
% 1.56/1.00  --inst_activity_threshold               500
% 1.56/1.00  --inst_out_proof                        true
% 1.56/1.00  
% 1.56/1.00  ------ Resolution Options
% 1.56/1.00  
% 1.56/1.00  --resolution_flag                       false
% 1.56/1.00  --res_lit_sel                           adaptive
% 1.56/1.00  --res_lit_sel_side                      none
% 1.56/1.00  --res_ordering                          kbo
% 1.56/1.00  --res_to_prop_solver                    active
% 1.56/1.00  --res_prop_simpl_new                    false
% 1.56/1.00  --res_prop_simpl_given                  true
% 1.56/1.00  --res_passive_queue_type                priority_queues
% 1.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/1.00  --res_passive_queues_freq               [15;5]
% 1.56/1.00  --res_forward_subs                      full
% 1.56/1.00  --res_backward_subs                     full
% 1.56/1.00  --res_forward_subs_resolution           true
% 1.56/1.00  --res_backward_subs_resolution          true
% 1.56/1.00  --res_orphan_elimination                true
% 1.56/1.00  --res_time_limit                        2.
% 1.56/1.00  --res_out_proof                         true
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Options
% 1.56/1.00  
% 1.56/1.00  --superposition_flag                    true
% 1.56/1.00  --sup_passive_queue_type                priority_queues
% 1.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.56/1.00  --demod_completeness_check              fast
% 1.56/1.00  --demod_use_ground                      true
% 1.56/1.00  --sup_to_prop_solver                    passive
% 1.56/1.00  --sup_prop_simpl_new                    true
% 1.56/1.00  --sup_prop_simpl_given                  true
% 1.56/1.00  --sup_fun_splitting                     false
% 1.56/1.00  --sup_smt_interval                      50000
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Simplification Setup
% 1.56/1.00  
% 1.56/1.00  --sup_indices_passive                   []
% 1.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_full_bw                           [BwDemod]
% 1.56/1.00  --sup_immed_triv                        [TrivRules]
% 1.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_immed_bw_main                     []
% 1.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  
% 1.56/1.00  ------ Combination Options
% 1.56/1.00  
% 1.56/1.00  --comb_res_mult                         3
% 1.56/1.00  --comb_sup_mult                         2
% 1.56/1.00  --comb_inst_mult                        10
% 1.56/1.00  
% 1.56/1.00  ------ Debug Options
% 1.56/1.00  
% 1.56/1.00  --dbg_backtrace                         false
% 1.56/1.00  --dbg_dump_prop_clauses                 false
% 1.56/1.00  --dbg_dump_prop_clauses_file            -
% 1.56/1.00  --dbg_out_stat                          false
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  ------ Proving...
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  % SZS status Theorem for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  fof(f4,axiom,(
% 1.56/1.00    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f10,plain,(
% 1.56/1.00    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(ennf_transformation,[],[f4])).
% 1.56/1.00  
% 1.56/1.00  fof(f24,plain,(
% 1.56/1.00    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(nnf_transformation,[],[f10])).
% 1.56/1.00  
% 1.56/1.00  fof(f25,plain,(
% 1.56/1.00    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(rectify,[],[f24])).
% 1.56/1.00  
% 1.56/1.00  fof(f26,plain,(
% 1.56/1.00    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0))))),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f27,plain,(
% 1.56/1.00    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).
% 1.56/1.00  
% 1.56/1.00  fof(f46,plain,(
% 1.56/1.00    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f27])).
% 1.56/1.00  
% 1.56/1.00  fof(f6,conjecture,(
% 1.56/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f7,negated_conjecture,(
% 1.56/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 1.56/1.00    inference(negated_conjecture,[],[f6])).
% 1.56/1.00  
% 1.56/1.00  fof(f13,plain,(
% 1.56/1.00    ? [X0,X1,X2] : ((~r2_hidden(k4_tarski(X0,X1),X2) & (! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 1.56/1.00    inference(ennf_transformation,[],[f7])).
% 1.56/1.00  
% 1.56/1.00  fof(f14,plain,(
% 1.56/1.00    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.56/1.00    inference(flattening,[],[f13])).
% 1.56/1.00  
% 1.56/1.00  fof(f29,plain,(
% 1.56/1.00    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r2_hidden(k4_tarski(sK3,sK4),sK5) & ! [X3] : ((sK4 != X3 & r2_hidden(k4_tarski(X3,sK4),sK5)) | ~r2_hidden(X3,k1_wellord1(sK5,sK3))) & r2_hidden(sK4,k3_relat_1(sK5)) & r2_hidden(sK3,k3_relat_1(sK5)) & v2_wellord1(sK5) & v1_relat_1(sK5))),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f30,plain,(
% 1.56/1.00    ~r2_hidden(k4_tarski(sK3,sK4),sK5) & ! [X3] : ((sK4 != X3 & r2_hidden(k4_tarski(X3,sK4),sK5)) | ~r2_hidden(X3,k1_wellord1(sK5,sK3))) & r2_hidden(sK4,k3_relat_1(sK5)) & r2_hidden(sK3,k3_relat_1(sK5)) & v2_wellord1(sK5) & v1_relat_1(sK5)),
% 1.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f54,plain,(
% 1.56/1.00    v1_relat_1(sK5)),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f55,plain,(
% 1.56/1.00    v2_wellord1(sK5)),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f3,axiom,(
% 1.56/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f9,plain,(
% 1.56/1.00    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(ennf_transformation,[],[f3])).
% 1.56/1.00  
% 1.56/1.00  fof(f22,plain,(
% 1.56/1.00    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(nnf_transformation,[],[f9])).
% 1.56/1.00  
% 1.56/1.00  fof(f23,plain,(
% 1.56/1.00    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(flattening,[],[f22])).
% 1.56/1.00  
% 1.56/1.00  fof(f43,plain,(
% 1.56/1.00    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f23])).
% 1.56/1.00  
% 1.56/1.00  fof(f60,plain,(
% 1.56/1.00    ~r2_hidden(k4_tarski(sK3,sK4),sK5)),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f56,plain,(
% 1.56/1.00    r2_hidden(sK3,k3_relat_1(sK5))),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f57,plain,(
% 1.56/1.00    r2_hidden(sK4,k3_relat_1(sK5))),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f59,plain,(
% 1.56/1.00    ( ! [X3] : (sK4 != X3 | ~r2_hidden(X3,k1_wellord1(sK5,sK3))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f30])).
% 1.56/1.00  
% 1.56/1.00  fof(f67,plain,(
% 1.56/1.00    ~r2_hidden(sK4,k1_wellord1(sK5,sK3))),
% 1.56/1.00    inference(equality_resolution,[],[f59])).
% 1.56/1.00  
% 1.56/1.00  fof(f2,axiom,(
% 1.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f8,plain,(
% 1.56/1.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(ennf_transformation,[],[f2])).
% 1.56/1.00  
% 1.56/1.00  fof(f17,plain,(
% 1.56/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(nnf_transformation,[],[f8])).
% 1.56/1.00  
% 1.56/1.00  fof(f18,plain,(
% 1.56/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(flattening,[],[f17])).
% 1.56/1.00  
% 1.56/1.00  fof(f19,plain,(
% 1.56/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(rectify,[],[f18])).
% 1.56/1.00  
% 1.56/1.00  fof(f20,plain,(
% 1.56/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f21,plain,(
% 1.56/1.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 1.56/1.00  
% 1.56/1.00  fof(f36,plain,(
% 1.56/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f21])).
% 1.56/1.00  
% 1.56/1.00  fof(f63,plain,(
% 1.56/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 1.56/1.00    inference(equality_resolution,[],[f36])).
% 1.56/1.00  
% 1.56/1.00  fof(f1,axiom,(
% 1.56/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f15,plain,(
% 1.56/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/1.00    inference(nnf_transformation,[],[f1])).
% 1.56/1.00  
% 1.56/1.00  fof(f16,plain,(
% 1.56/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/1.00    inference(flattening,[],[f15])).
% 1.56/1.00  
% 1.56/1.00  fof(f31,plain,(
% 1.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.56/1.00    inference(cnf_transformation,[],[f16])).
% 1.56/1.00  
% 1.56/1.00  fof(f62,plain,(
% 1.56/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/1.00    inference(equality_resolution,[],[f31])).
% 1.56/1.00  
% 1.56/1.00  fof(f5,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f11,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(ennf_transformation,[],[f5])).
% 1.56/1.00  
% 1.56/1.00  fof(f12,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(flattening,[],[f11])).
% 1.56/1.00  
% 1.56/1.00  fof(f28,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(nnf_transformation,[],[f12])).
% 1.56/1.00  
% 1.56/1.00  fof(f53,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f28])).
% 1.56/1.00  
% 1.56/1.00  cnf(c_20,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | ~ v6_relat_2(X1)
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | X2 = X0 ),
% 1.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_29,negated_conjecture,
% 1.56/1.00      ( v1_relat_1(sK5) ),
% 1.56/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_452,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 1.56/1.00      | ~ v6_relat_2(X1)
% 1.56/1.00      | X2 = X0
% 1.56/1.00      | sK5 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_453,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | r2_hidden(k4_tarski(X1,X0),sK5)
% 1.56/1.00      | ~ v6_relat_2(sK5)
% 1.56/1.00      | X0 = X1 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_452]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_28,negated_conjecture,
% 1.56/1.00      ( v2_wellord1(sK5) ),
% 1.56/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_11,plain,
% 1.56/1.00      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_73,plain,
% 1.56/1.00      ( v6_relat_2(sK5) | ~ v2_wellord1(sK5) | ~ v1_relat_1(sK5) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_457,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(X1,X0),sK5)
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | X0 = X1 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_453,c_29,c_28,c_73]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_458,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | r2_hidden(k4_tarski(X1,X0),sK5)
% 1.56/1.00      | X0 = X1 ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_457]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_922,plain,
% 1.56/1.00      ( X0 = X1
% 1.56/1.00      | r2_hidden(X0,k3_relat_1(sK5)) != iProver_top
% 1.56/1.00      | r2_hidden(X1,k3_relat_1(sK5)) != iProver_top
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) = iProver_top
% 1.56/1.00      | r2_hidden(k4_tarski(X1,X0),sK5) = iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_23,negated_conjecture,
% 1.56/1.00      ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5) ),
% 1.56/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_932,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(sK3,sK4),sK5) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1711,plain,
% 1.56/1.00      ( sK4 = sK3
% 1.56/1.00      | r2_hidden(k4_tarski(sK4,sK3),sK5) = iProver_top
% 1.56/1.00      | r2_hidden(sK4,k3_relat_1(sK5)) != iProver_top
% 1.56/1.00      | r2_hidden(sK3,k3_relat_1(sK5)) != iProver_top ),
% 1.56/1.00      inference(superposition,[status(thm)],[c_922,c_932]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_27,negated_conjecture,
% 1.56/1.00      ( r2_hidden(sK3,k3_relat_1(sK5)) ),
% 1.56/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_26,negated_conjecture,
% 1.56/1.00      ( r2_hidden(sK4,k3_relat_1(sK5)) ),
% 1.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_24,negated_conjecture,
% 1.56/1.00      ( ~ r2_hidden(sK4,k1_wellord1(sK5,sK3)) ),
% 1.56/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_649,plain,( X0 = X0 ),theory(equality) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1103,plain,
% 1.56/1.00      ( sK4 = sK4 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_649]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_6,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | X0 = X2 ),
% 1.56/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_498,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | X2 = X0
% 1.56/1.00      | sK5 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_499,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_wellord1(sK5,X1))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | X1 = X0 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1095,plain,
% 1.56/1.00      ( ~ r2_hidden(k4_tarski(sK4,X0),sK5)
% 1.56/1.00      | r2_hidden(sK4,k1_wellord1(sK5,X0))
% 1.56/1.00      | X0 = sK4 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_499]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1396,plain,
% 1.56/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK3),sK5)
% 1.56/1.00      | r2_hidden(sK4,k1_wellord1(sK5,sK3))
% 1.56/1.00      | sK3 = sK4 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1756,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(sK4,sK3),sK5)
% 1.56/1.00      | ~ r2_hidden(sK4,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(sK3,k3_relat_1(sK5))
% 1.56/1.00      | sK4 = sK3 ),
% 1.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1711]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_650,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1143,plain,
% 1.56/1.00      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_650]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1424,plain,
% 1.56/1.00      ( X0 != sK4 | X0 = sK3 | sK3 != sK4 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1143]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1795,plain,
% 1.56/1.00      ( sK4 != sK4 | sK4 = sK3 | sK3 != sK4 ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1424]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1955,plain,
% 1.56/1.00      ( sK4 = sK3 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1711,c_27,c_26,c_24,c_1103,c_1396,c_1756,c_1795]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1960,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(sK3,sK3),sK5) != iProver_top ),
% 1.56/1.00      inference(demodulation,[status(thm)],[c_1955,c_932]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_2,plain,
% 1.56/1.00      ( r1_tarski(X0,X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1404,plain,
% 1.56/1.00      ( r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1405,plain,
% 1.56/1.00      ( r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) = iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_21,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X0))
% 1.56/1.00      | ~ v2_wellord1(X1)
% 1.56/1.00      | ~ v1_relat_1(X1) ),
% 1.56/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_358,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(X2,k3_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X0))
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | sK5 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_359,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1))
% 1.56/1.00      | ~ v1_relat_1(sK5) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_363,plain,
% 1.56/1.00      ( ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X0,k3_relat_1(sK5)) ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_359,c_29]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_364,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | ~ r2_hidden(X1,k3_relat_1(sK5))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,X1),sK5)
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(sK5,X0),k1_wellord1(sK5,X1)) ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_363]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1062,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k3_relat_1(sK5))
% 1.56/1.00      | r2_hidden(k4_tarski(sK3,X0),sK5)
% 1.56/1.00      | ~ r2_hidden(sK3,k3_relat_1(sK5))
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,X0)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1205,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(sK3,sK3),sK5)
% 1.56/1.00      | ~ r2_hidden(sK3,k3_relat_1(sK5))
% 1.56/1.00      | ~ r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_1062]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1206,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(sK3,sK3),sK5) = iProver_top
% 1.56/1.00      | r2_hidden(sK3,k3_relat_1(sK5)) != iProver_top
% 1.56/1.00      | r1_tarski(k1_wellord1(sK5,sK3),k1_wellord1(sK5,sK3)) != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_32,plain,
% 1.56/1.00      ( r2_hidden(sK3,k3_relat_1(sK5)) = iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(contradiction,plain,
% 1.56/1.00      ( $false ),
% 1.56/1.00      inference(minisat,[status(thm)],[c_1960,c_1405,c_1206,c_32]) ).
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  ------                               Statistics
% 1.56/1.00  
% 1.56/1.00  ------ General
% 1.56/1.00  
% 1.56/1.00  abstr_ref_over_cycles:                  0
% 1.56/1.00  abstr_ref_under_cycles:                 0
% 1.56/1.00  gc_basic_clause_elim:                   0
% 1.56/1.00  forced_gc_time:                         0
% 1.56/1.00  parsing_time:                           0.012
% 1.56/1.00  unif_index_cands_time:                  0.
% 1.56/1.00  unif_index_add_time:                    0.
% 1.56/1.00  orderings_time:                         0.
% 1.56/1.00  out_proof_time:                         0.021
% 1.56/1.00  total_time:                             0.104
% 1.56/1.00  num_of_symbols:                         49
% 1.56/1.00  num_of_terms:                           1497
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing
% 1.56/1.00  
% 1.56/1.00  num_of_splits:                          0
% 1.56/1.00  num_of_split_atoms:                     0
% 1.56/1.00  num_of_reused_defs:                     0
% 1.56/1.00  num_eq_ax_congr_red:                    14
% 1.56/1.00  num_of_sem_filtered_clauses:            1
% 1.56/1.00  num_of_subtypes:                        0
% 1.56/1.00  monotx_restored_types:                  0
% 1.56/1.00  sat_num_of_epr_types:                   0
% 1.56/1.00  sat_num_of_non_cyclic_types:            0
% 1.56/1.00  sat_guarded_non_collapsed_types:        0
% 1.56/1.00  num_pure_diseq_elim:                    0
% 1.56/1.00  simp_replaced_by:                       0
% 1.56/1.00  res_preprocessed:                       94
% 1.56/1.00  prep_upred:                             0
% 1.56/1.00  prep_unflattend:                        15
% 1.56/1.00  smt_new_axioms:                         0
% 1.56/1.00  pred_elim_cands:                        2
% 1.56/1.00  pred_elim:                              7
% 1.56/1.00  pred_elim_cl:                           13
% 1.56/1.00  pred_elim_cycles:                       9
% 1.56/1.00  merged_defs:                            0
% 1.56/1.00  merged_defs_ncl:                        0
% 1.56/1.00  bin_hyper_res:                          0
% 1.56/1.00  prep_cycles:                            4
% 1.56/1.00  pred_elim_time:                         0.005
% 1.56/1.00  splitting_time:                         0.
% 1.56/1.00  sem_filter_time:                        0.
% 1.56/1.00  monotx_time:                            0.001
% 1.56/1.00  subtype_inf_time:                       0.
% 1.56/1.00  
% 1.56/1.00  ------ Problem properties
% 1.56/1.00  
% 1.56/1.00  clauses:                                16
% 1.56/1.00  conjectures:                            5
% 1.56/1.00  epr:                                    2
% 1.56/1.00  horn:                                   11
% 1.56/1.00  ground:                                 4
% 1.56/1.00  unary:                                  6
% 1.56/1.00  binary:                                 2
% 1.56/1.00  lits:                                   39
% 1.56/1.00  lits_eq:                                8
% 1.56/1.00  fd_pure:                                0
% 1.56/1.00  fd_pseudo:                              0
% 1.56/1.00  fd_cond:                                0
% 1.56/1.00  fd_pseudo_cond:                         5
% 1.56/1.00  ac_symbols:                             0
% 1.56/1.00  
% 1.56/1.00  ------ Propositional Solver
% 1.56/1.00  
% 1.56/1.00  prop_solver_calls:                      26
% 1.56/1.00  prop_fast_solver_calls:                 602
% 1.56/1.00  smt_solver_calls:                       0
% 1.56/1.00  smt_fast_solver_calls:                  0
% 1.56/1.00  prop_num_of_clauses:                    610
% 1.56/1.00  prop_preprocess_simplified:             3058
% 1.56/1.00  prop_fo_subsumed:                       7
% 1.56/1.00  prop_solver_time:                       0.
% 1.56/1.00  smt_solver_time:                        0.
% 1.56/1.00  smt_fast_solver_time:                   0.
% 1.56/1.00  prop_fast_solver_time:                  0.
% 1.56/1.00  prop_unsat_core_time:                   0.
% 1.56/1.00  
% 1.56/1.00  ------ QBF
% 1.56/1.00  
% 1.56/1.00  qbf_q_res:                              0
% 1.56/1.00  qbf_num_tautologies:                    0
% 1.56/1.00  qbf_prep_cycles:                        0
% 1.56/1.00  
% 1.56/1.00  ------ BMC1
% 1.56/1.00  
% 1.56/1.00  bmc1_current_bound:                     -1
% 1.56/1.00  bmc1_last_solved_bound:                 -1
% 1.56/1.00  bmc1_unsat_core_size:                   -1
% 1.56/1.00  bmc1_unsat_core_parents_size:           -1
% 1.56/1.00  bmc1_merge_next_fun:                    0
% 1.56/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation
% 1.56/1.00  
% 1.56/1.00  inst_num_of_clauses:                    149
% 1.56/1.00  inst_num_in_passive:                    17
% 1.56/1.00  inst_num_in_active:                     85
% 1.56/1.00  inst_num_in_unprocessed:                47
% 1.56/1.00  inst_num_of_loops:                      100
% 1.56/1.00  inst_num_of_learning_restarts:          0
% 1.56/1.00  inst_num_moves_active_passive:          13
% 1.56/1.00  inst_lit_activity:                      0
% 1.56/1.00  inst_lit_activity_moves:                0
% 1.56/1.00  inst_num_tautologies:                   0
% 1.56/1.00  inst_num_prop_implied:                  0
% 1.56/1.00  inst_num_existing_simplified:           0
% 1.56/1.00  inst_num_eq_res_simplified:             0
% 1.56/1.00  inst_num_child_elim:                    0
% 1.56/1.00  inst_num_of_dismatching_blockings:      19
% 1.56/1.00  inst_num_of_non_proper_insts:           128
% 1.56/1.00  inst_num_of_duplicates:                 0
% 1.56/1.00  inst_inst_num_from_inst_to_res:         0
% 1.56/1.00  inst_dismatching_checking_time:         0.
% 1.56/1.00  
% 1.56/1.00  ------ Resolution
% 1.56/1.00  
% 1.56/1.00  res_num_of_clauses:                     0
% 1.56/1.00  res_num_in_passive:                     0
% 1.56/1.00  res_num_in_active:                      0
% 1.56/1.00  res_num_of_loops:                       98
% 1.56/1.00  res_forward_subset_subsumed:            34
% 1.56/1.00  res_backward_subset_subsumed:           0
% 1.56/1.00  res_forward_subsumed:                   0
% 1.56/1.00  res_backward_subsumed:                  0
% 1.56/1.00  res_forward_subsumption_resolution:     0
% 1.56/1.00  res_backward_subsumption_resolution:    0
% 1.56/1.00  res_clause_to_clause_subsumption:       121
% 1.56/1.00  res_orphan_elimination:                 0
% 1.56/1.00  res_tautology_del:                      5
% 1.56/1.00  res_num_eq_res_simplified:              0
% 1.56/1.00  res_num_sel_changes:                    0
% 1.56/1.00  res_moves_from_active_to_pass:          0
% 1.56/1.00  
% 1.56/1.00  ------ Superposition
% 1.56/1.00  
% 1.56/1.00  sup_time_total:                         0.
% 1.56/1.00  sup_time_generating:                    0.
% 1.56/1.00  sup_time_sim_full:                      0.
% 1.56/1.00  sup_time_sim_immed:                     0.
% 1.56/1.00  
% 1.56/1.00  sup_num_of_clauses:                     28
% 1.56/1.00  sup_num_in_active:                      13
% 1.56/1.00  sup_num_in_passive:                     15
% 1.56/1.00  sup_num_of_loops:                       18
% 1.56/1.00  sup_fw_superposition:                   4
% 1.56/1.00  sup_bw_superposition:                   15
% 1.56/1.00  sup_immediate_simplified:               3
% 1.56/1.00  sup_given_eliminated:                   0
% 1.56/1.00  comparisons_done:                       0
% 1.56/1.00  comparisons_avoided:                    0
% 1.56/1.00  
% 1.56/1.00  ------ Simplifications
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  sim_fw_subset_subsumed:                 0
% 1.56/1.00  sim_bw_subset_subsumed:                 0
% 1.56/1.00  sim_fw_subsumed:                        3
% 1.56/1.00  sim_bw_subsumed:                        0
% 1.56/1.00  sim_fw_subsumption_res:                 1
% 1.56/1.00  sim_bw_subsumption_res:                 0
% 1.56/1.00  sim_tautology_del:                      2
% 1.56/1.00  sim_eq_tautology_del:                   2
% 1.56/1.00  sim_eq_res_simp:                        1
% 1.56/1.00  sim_fw_demodulated:                     0
% 1.56/1.00  sim_bw_demodulated:                     5
% 1.56/1.00  sim_light_normalised:                   0
% 1.56/1.00  sim_joinable_taut:                      0
% 1.56/1.00  sim_joinable_simp:                      0
% 1.56/1.00  sim_ac_normalised:                      0
% 1.56/1.00  sim_smt_subsumption:                    0
% 1.56/1.00  
%------------------------------------------------------------------------------
