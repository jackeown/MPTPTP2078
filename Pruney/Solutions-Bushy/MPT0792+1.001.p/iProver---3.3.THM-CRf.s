%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0792+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 266 expanded)
%              Number of clauses        :   44 (  70 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  426 (1738 expanded)
%              Number of equality atoms :   91 ( 221 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & sK2(X0) != sK3(X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0))
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & sK2(X0) != sK3(X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0))
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f26])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f28,plain,
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
   => ( ~ r2_hidden(k4_tarski(sK4,sK5),sK6)
      & ! [X3] :
          ( ( sK5 != X3
            & r2_hidden(k4_tarski(X3,sK5),sK6) )
          | ~ r2_hidden(X3,k1_wellord1(sK6,sK4)) )
      & r2_hidden(sK5,k3_relat_1(sK6))
      & r2_hidden(sK4,k3_relat_1(sK6))
      & v2_wellord1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),sK6)
    & ! [X3] :
        ( ( sK5 != X3
          & r2_hidden(k4_tarski(X3,sK5),sK6) )
        | ~ r2_hidden(X3,k1_wellord1(sK6,sK4)) )
    & r2_hidden(sK5,k3_relat_1(sK6))
    & r2_hidden(sK4,k3_relat_1(sK6))
    & v2_wellord1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f28])).

fof(f51,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    v2_wellord1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ~ r2_hidden(k4_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    r2_hidden(sK4,k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    r2_hidden(sK5,k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f56,plain,(
    ! [X3] :
      ( sK5 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK6,sK4)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ~ r2_hidden(sK5,k1_wellord1(sK6,sK4)) ),
    inference(equality_resolution,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_458,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_459,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(X1,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X1,X0),sK6)
    | r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v6_relat_2(sK6)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_26,negated_conjecture,
    ( v2_wellord1(sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_74,plain,
    ( v6_relat_2(sK6)
    | ~ v2_wellord1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_461,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6)
    | r2_hidden(k4_tarski(X1,X0),sK6)
    | ~ r2_hidden(X1,k3_relat_1(sK6))
    | ~ r2_hidden(X0,k3_relat_1(sK6))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_27,c_26,c_74])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | ~ r2_hidden(X1,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X1,X0),sK6)
    | r2_hidden(k4_tarski(X0,X1),sK6)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_868,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_877,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1549,plain,
    ( sK5 = sK4
    | r2_hidden(k4_tarski(sK5,sK4),sK6) = iProver_top
    | r2_hidden(sK5,k3_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4,k3_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_877])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,plain,
    ( r2_hidden(sK4,k3_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,k3_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( r2_hidden(sK5,k3_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1694,plain,
    ( sK5 = sK4
    | r2_hidden(k4_tarski(sK5,sK4),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1549,c_30,c_31])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_514,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_515,plain,
    ( r2_hidden(X0,k1_wellord1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_865,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK6,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1700,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_wellord1(sK6,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_865])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK5,k1_wellord1(sK6,sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,plain,
    ( r2_hidden(sK5,k1_wellord1(sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1703,plain,
    ( sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1700,c_35])).

cnf(c_1708,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1703,c_877])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_481,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,X0),sK6)
    | ~ v1_relat_2(sK6) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_11,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_306,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_307,plain,
    ( v1_relat_2(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_65,plain,
    ( v1_relat_2(sK6)
    | ~ v2_wellord1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_309,plain,
    ( v1_relat_2(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_27,c_26,c_65])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_309])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,X0),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK6)
    | ~ r2_hidden(X0,k3_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,X0),sK6) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_484,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK6)
    | ~ r2_hidden(X0,k3_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_27,c_369])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,X0),sK6) ),
    inference(renaming,[status(thm)],[c_484])).

cnf(c_966,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),sK6)
    | ~ r2_hidden(sK4,k3_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_967,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),sK6) = iProver_top
    | r2_hidden(sK4,k3_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1708,c_967,c_30])).


%------------------------------------------------------------------------------
