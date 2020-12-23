%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:31 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 797 expanded)
%              Number of clauses        :  104 ( 230 expanded)
%              Number of leaves         :   20 ( 137 expanded)
%              Depth                    :   29
%              Number of atoms          :  722 (4748 expanded)
%              Number of equality atoms :  231 ( 807 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
        | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
        | r2_hidden(k4_tarski(sK5,sK6),sK7) )
      & r2_hidden(sK6,k3_relat_1(sK7))
      & r2_hidden(sK5,k3_relat_1(sK7))
      & v2_wellord1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
      | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
      | r2_hidden(k4_tarski(sK5,sK6),sK7) )
    & r2_hidden(sK6,k3_relat_1(sK7))
    & r2_hidden(sK5,k3_relat_1(sK7))
    & v2_wellord1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f51])).

fof(f90,plain,
    ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    r2_hidden(sK5,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f97,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).

fof(f76,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f73,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,
    ( ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2046,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2038,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_30,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2027,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7)
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2024,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2049,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,negated_conjecture,
    ( v2_wellord1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_517,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
    | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_38])).

cnf(c_2018,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),X1) = k1_wellord1(sK7,X1)
    | r2_hidden(X1,k1_wellord1(sK7,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_2670,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),X1)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),X1))
    | r1_tarski(k1_wellord1(sK7,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2018])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2045,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3603,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X2,X0)),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_2045])).

cnf(c_6570,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X3,X0)),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_2045])).

cnf(c_11649,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),X1)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),X1))
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X3,k1_wellord1(sK7,X0))),X2) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2670,c_6570])).

cnf(c_19379,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK5))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK5)))
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(X1,k1_wellord1(sK7,X0))),k1_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2024,c_11649])).

cnf(c_39,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_40,plain,
    ( v2_wellord1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK5,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( r2_hidden(sK5,k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK6,k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( r2_hidden(sK6,k3_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_88,plain,
    ( v1_relat_2(sK7)
    | ~ v2_wellord1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_87,plain,
    ( v1_relat_2(X0) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_89,plain,
    ( v1_relat_2(sK7) = iProver_top
    | v2_wellord1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_15,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_96,plain,
    ( v6_relat_2(X0) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_98,plain,
    ( v6_relat_2(sK7) = iProver_top
    | v2_wellord1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_121,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_125,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2108,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK7,X0))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2248,plain,
    ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_2251,plain,
    ( r2_hidden(sK6,k1_wellord1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_2648,plain,
    ( ~ r2_hidden(sK5,k1_wellord1(sK7,sK5))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2289,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK6),X1)
    | r2_hidden(k4_tarski(sK6,X0),X1)
    | ~ r2_hidden(sK6,k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2853,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK7)
    | r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r2_hidden(sK6,k3_relat_1(sK7))
    | ~ r2_hidden(sK5,k3_relat_1(sK7))
    | ~ v6_relat_2(sK7)
    | ~ v1_relat_1(sK7)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_2854,plain,
    ( sK5 = sK6
    | r2_hidden(k4_tarski(sK6,sK5),sK7) = iProver_top
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5,k3_relat_1(sK7)) != iProver_top
    | v6_relat_2(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2853])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3290,plain,
    ( r2_hidden(k4_tarski(sK6,sK6),sK7)
    | ~ r2_hidden(sK6,k3_relat_1(sK7))
    | ~ v1_relat_2(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3291,plain,
    ( r2_hidden(k4_tarski(sK6,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top
    | v1_relat_2(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3290])).

cnf(c_3293,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK7)
    | ~ r2_hidden(sK5,k3_relat_1(sK7))
    | ~ v1_relat_2(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2772,plain,
    ( ~ r2_hidden(k4_tarski(sK6,X0),X1)
    | r2_hidden(sK6,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4535,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
    | r2_hidden(sK6,k1_wellord1(sK7,sK6))
    | ~ v1_relat_1(sK7)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_2789,plain,
    ( ~ r2_hidden(k4_tarski(sK5,X0),X1)
    | r2_hidden(sK5,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4552,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK5),sK7)
    | r2_hidden(sK5,k1_wellord1(sK7,sK5))
    | ~ v1_relat_1(sK7)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2111,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_wellord1(sK7,X2))
    | ~ r1_tarski(X1,k1_wellord1(sK7,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2235,plain,
    ( ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
    | r2_hidden(sK6,k1_wellord1(sK7,X1))
    | ~ r1_tarski(k1_wellord1(sK7,X0),k1_wellord1(sK7,X1)) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_2753,plain,
    ( ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
    | r2_hidden(sK6,k1_wellord1(sK7,sK6))
    | ~ r1_tarski(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2235])).

cnf(c_4848,plain,
    ( r2_hidden(sK6,k1_wellord1(sK7,sK6))
    | ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_4849,plain,
    ( r2_hidden(sK6,k1_wellord1(sK7,sK6)) = iProver_top
    | r2_hidden(sK6,k1_wellord1(sK7,sK5)) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4848])).

cnf(c_2317,plain,
    ( r2_hidden(X0,k1_wellord1(X1,sK5))
    | ~ r2_hidden(k4_tarski(X0,sK5),X1)
    | ~ v1_relat_1(X1)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4873,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK5),sK7)
    | r2_hidden(sK6,k1_wellord1(sK7,sK5))
    | ~ v1_relat_1(sK7)
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_4874,plain,
    ( sK6 = sK5
    | r2_hidden(k4_tarski(sK6,sK5),sK7) != iProver_top
    | r2_hidden(sK6,k1_wellord1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4873])).

cnf(c_1321,plain,
    ( X0 != X1
    | X2 != X3
    | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
    theory(equality)).

cnf(c_2439,plain,
    ( k4_tarski(sK5,sK6) = k4_tarski(X0,X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2944,plain,
    ( k4_tarski(sK5,sK6) = k4_tarski(X0,sK6)
    | sK6 != sK6
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2439])).

cnf(c_8743,plain,
    ( k4_tarski(sK5,sK6) = k4_tarski(sK6,sK6)
    | sK6 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2944])).

cnf(c_1317,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2799,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_4387,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_8835,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4387])).

cnf(c_1319,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2135,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK5,sK6),sK7)
    | k4_tarski(sK5,sK6) != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2181,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(sK5,sK6),sK7)
    | k4_tarski(sK5,sK6) != k4_tarski(X0,X1)
    | sK7 != X2 ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_19322,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK6),X0)
    | r2_hidden(k4_tarski(sK5,sK6),sK7)
    | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_19323,plain,
    ( k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
    | sK7 != X0
    | r2_hidden(k4_tarski(sK6,sK6),X0) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19322])).

cnf(c_19325,plain,
    ( k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
    | sK7 != sK7
    | r2_hidden(k4_tarski(sK6,sK6),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19323])).

cnf(c_19464,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19379,c_38,c_39,c_37,c_40,c_36,c_41,c_35,c_42,c_43,c_88,c_89,c_98,c_121,c_125,c_2248,c_2251,c_2648,c_2854,c_3290,c_3291,c_3293,c_4535,c_4552,c_4849,c_4874,c_8743,c_8835,c_19325])).

cnf(c_2041,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19469,plain,
    ( sK6 = sK5
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_19464,c_2041])).

cnf(c_19627,plain,
    ( r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19469,c_39])).

cnf(c_19628,plain,
    ( sK6 = sK5
    | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_19627])).

cnf(c_19633,plain,
    ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK5) = k1_wellord1(sK7,sK5)
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_19628,c_2018])).

cnf(c_29,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2028,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3602,plain,
    ( r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
    | r1_tarski(k3_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2045])).

cnf(c_19968,plain,
    ( sK6 = sK5
    | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))),X0) != iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19633,c_3602])).

cnf(c_21971,plain,
    ( sK6 = sK5
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_19968])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
    | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22100,plain,
    ( v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
    | sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21971,c_38,c_39,c_37,c_40,c_36,c_41,c_35,c_42,c_43,c_44,c_88,c_89,c_98,c_121,c_125,c_2248,c_2251,c_2648,c_2854,c_3290,c_3291,c_3293,c_4535,c_4552,c_4849,c_4874,c_8743,c_8835,c_19325])).

cnf(c_22101,plain,
    ( sK6 = sK5
    | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22100])).

cnf(c_22104,plain,
    ( sK6 = sK5
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_22101])).

cnf(c_22107,plain,
    ( sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22104,c_39])).

cnf(c_2025,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22125,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK7) != iProver_top
    | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22107,c_2025])).

cnf(c_3294,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK7) = iProver_top
    | r2_hidden(sK5,k3_relat_1(sK7)) != iProver_top
    | v1_relat_2(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3293])).

cnf(c_22285,plain,
    ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22125,c_39,c_40,c_41,c_89,c_3294])).

cnf(c_22289,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2046,c_22285])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.36/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.49  
% 7.36/1.49  ------  iProver source info
% 7.36/1.49  
% 7.36/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.49  git: non_committed_changes: false
% 7.36/1.49  git: last_make_outside_of_git: false
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     num_symb
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       true
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  ------ Parsing...
% 7.36/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.49  ------ Proving...
% 7.36/1.49  ------ Problem Properties 
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  clauses                                 33
% 7.36/1.49  conjectures                             5
% 7.36/1.49  EPR                                     7
% 7.36/1.49  Horn                                    23
% 7.36/1.49  unary                                   6
% 7.36/1.49  binary                                  10
% 7.36/1.49  lits                                    87
% 7.36/1.49  lits eq                                 10
% 7.36/1.49  fd_pure                                 0
% 7.36/1.49  fd_pseudo                               0
% 7.36/1.49  fd_cond                                 0
% 7.36/1.49  fd_pseudo_cond                          5
% 7.36/1.49  AC symbols                              0
% 7.36/1.49  
% 7.36/1.49  ------ Schedule dynamic 5 is on 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  Current options:
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     none
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       false
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ Proving...
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  % SZS status Theorem for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49   Resolution empty clause
% 7.36/1.49  
% 7.36/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  fof(f2,axiom,(
% 7.36/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f32,plain,(
% 7.36/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.49    inference(nnf_transformation,[],[f2])).
% 7.36/1.49  
% 7.36/1.49  fof(f33,plain,(
% 7.36/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.36/1.49    inference(flattening,[],[f32])).
% 7.36/1.49  
% 7.36/1.49  fof(f56,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.36/1.49    inference(cnf_transformation,[],[f33])).
% 7.36/1.49  
% 7.36/1.49  fof(f93,plain,(
% 7.36/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.36/1.49    inference(equality_resolution,[],[f56])).
% 7.36/1.49  
% 7.36/1.49  fof(f6,axiom,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f19,plain,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f6])).
% 7.36/1.49  
% 7.36/1.49  fof(f72,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f19])).
% 7.36/1.49  
% 7.36/1.49  fof(f10,axiom,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f23,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(ennf_transformation,[],[f10])).
% 7.36/1.49  
% 7.36/1.49  fof(f84,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f23])).
% 7.36/1.49  
% 7.36/1.49  fof(f12,conjecture,(
% 7.36/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f13,negated_conjecture,(
% 7.36/1.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.36/1.49    inference(negated_conjecture,[],[f12])).
% 7.36/1.49  
% 7.36/1.49  fof(f26,plain,(
% 7.36/1.49    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 7.36/1.49    inference(ennf_transformation,[],[f13])).
% 7.36/1.49  
% 7.36/1.49  fof(f27,plain,(
% 7.36/1.49    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.36/1.49    inference(flattening,[],[f26])).
% 7.36/1.49  
% 7.36/1.49  fof(f49,plain,(
% 7.36/1.49    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.36/1.49    inference(nnf_transformation,[],[f27])).
% 7.36/1.49  
% 7.36/1.49  fof(f50,plain,(
% 7.36/1.49    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.36/1.49    inference(flattening,[],[f49])).
% 7.36/1.49  
% 7.36/1.49  fof(f51,plain,(
% 7.36/1.49    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & r2_hidden(sK6,k3_relat_1(sK7)) & r2_hidden(sK5,k3_relat_1(sK7)) & v2_wellord1(sK7) & v1_relat_1(sK7))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f52,plain,(
% 7.36/1.49    (~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)) & (r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)) & r2_hidden(sK6,k3_relat_1(sK7)) & r2_hidden(sK5,k3_relat_1(sK7)) & v2_wellord1(sK7) & v1_relat_1(sK7)),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f51])).
% 7.36/1.49  
% 7.36/1.49  fof(f90,plain,(
% 7.36/1.49    r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  fof(f1,axiom,(
% 7.36/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f14,plain,(
% 7.36/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f1])).
% 7.36/1.49  
% 7.36/1.49  fof(f28,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.49    inference(nnf_transformation,[],[f14])).
% 7.36/1.49  
% 7.36/1.49  fof(f29,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.49    inference(rectify,[],[f28])).
% 7.36/1.49  
% 7.36/1.49  fof(f30,plain,(
% 7.36/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f31,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.36/1.49  
% 7.36/1.49  fof(f54,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f31])).
% 7.36/1.49  
% 7.36/1.49  fof(f11,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f24,plain,(
% 7.36/1.49    ! [X0,X1,X2] : ((k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 7.36/1.49    inference(ennf_transformation,[],[f11])).
% 7.36/1.49  
% 7.36/1.49  fof(f25,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 7.36/1.49    inference(flattening,[],[f24])).
% 7.36/1.49  
% 7.36/1.49  fof(f85,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f25])).
% 7.36/1.49  
% 7.36/1.49  fof(f87,plain,(
% 7.36/1.49    v2_wellord1(sK7)),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  fof(f86,plain,(
% 7.36/1.49    v1_relat_1(sK7)),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  fof(f3,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f15,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.36/1.49    inference(ennf_transformation,[],[f3])).
% 7.36/1.49  
% 7.36/1.49  fof(f16,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.36/1.49    inference(flattening,[],[f15])).
% 7.36/1.49  
% 7.36/1.49  fof(f59,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f16])).
% 7.36/1.49  
% 7.36/1.49  fof(f88,plain,(
% 7.36/1.49    r2_hidden(sK5,k3_relat_1(sK7))),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  fof(f89,plain,(
% 7.36/1.49    r2_hidden(sK6,k3_relat_1(sK7))),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  fof(f5,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f18,plain,(
% 7.36/1.49    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f5])).
% 7.36/1.49  
% 7.36/1.49  fof(f39,plain,(
% 7.36/1.49    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f18])).
% 7.36/1.49  
% 7.36/1.49  fof(f40,plain,(
% 7.36/1.49    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(flattening,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f66,plain,(
% 7.36/1.49    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f40])).
% 7.36/1.49  
% 7.36/1.49  fof(f69,plain,(
% 7.36/1.49    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f40])).
% 7.36/1.49  
% 7.36/1.49  fof(f58,plain,(
% 7.36/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f33])).
% 7.36/1.49  
% 7.36/1.49  fof(f4,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f17,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f4])).
% 7.36/1.49  
% 7.36/1.49  fof(f34,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f17])).
% 7.36/1.49  
% 7.36/1.49  fof(f35,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(flattening,[],[f34])).
% 7.36/1.49  
% 7.36/1.49  fof(f36,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(rectify,[],[f35])).
% 7.36/1.49  
% 7.36/1.49  fof(f37,plain,(
% 7.36/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f38,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 7.36/1.49  
% 7.36/1.49  fof(f60,plain,(
% 7.36/1.49    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f38])).
% 7.36/1.49  
% 7.36/1.49  fof(f96,plain,(
% 7.36/1.49    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f60])).
% 7.36/1.49  
% 7.36/1.49  fof(f97,plain,(
% 7.36/1.49    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f96])).
% 7.36/1.49  
% 7.36/1.49  fof(f8,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f21,plain,(
% 7.36/1.49    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f8])).
% 7.36/1.49  
% 7.36/1.49  fof(f45,plain,(
% 7.36/1.49    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f21])).
% 7.36/1.49  
% 7.36/1.49  fof(f46,plain,(
% 7.36/1.49    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(rectify,[],[f45])).
% 7.36/1.49  
% 7.36/1.49  fof(f47,plain,(
% 7.36/1.49    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f48,plain,(
% 7.36/1.49    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).
% 7.36/1.49  
% 7.36/1.49  fof(f76,plain,(
% 7.36/1.49    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f48])).
% 7.36/1.49  
% 7.36/1.49  fof(f7,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f20,plain,(
% 7.36/1.49    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f7])).
% 7.36/1.49  
% 7.36/1.49  fof(f41,plain,(
% 7.36/1.49    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f20])).
% 7.36/1.49  
% 7.36/1.49  fof(f42,plain,(
% 7.36/1.49    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(rectify,[],[f41])).
% 7.36/1.49  
% 7.36/1.49  fof(f43,plain,(
% 7.36/1.49    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f44,plain,(
% 7.36/1.49    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 7.36/1.49  
% 7.36/1.49  fof(f73,plain,(
% 7.36/1.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f44])).
% 7.36/1.49  
% 7.36/1.49  fof(f62,plain,(
% 7.36/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f38])).
% 7.36/1.49  
% 7.36/1.49  fof(f94,plain,(
% 7.36/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f62])).
% 7.36/1.49  
% 7.36/1.49  fof(f53,plain,(
% 7.36/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f31])).
% 7.36/1.49  
% 7.36/1.49  fof(f9,axiom,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 7.36/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f22,plain,(
% 7.36/1.49    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(ennf_transformation,[],[f9])).
% 7.36/1.49  
% 7.36/1.49  fof(f82,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f22])).
% 7.36/1.49  
% 7.36/1.49  fof(f91,plain,(
% 7.36/1.49    ~r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) | ~r2_hidden(k4_tarski(sK5,sK6),sK7)),
% 7.36/1.49    inference(cnf_transformation,[],[f52])).
% 7.36/1.49  
% 7.36/1.49  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f93]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2046,plain,
% 7.36/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19,plain,
% 7.36/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2038,plain,
% 7.36/1.49      ( v1_relat_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_30,plain,
% 7.36/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2027,plain,
% 7.36/1.49      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) = iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_34,negated_conjecture,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2024,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1,plain,
% 7.36/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2049,plain,
% 7.36/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.36/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_32,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.36/1.49      | ~ v2_wellord1(X1)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_37,negated_conjecture,
% 7.36/1.49      ( v2_wellord1(sK7) ),
% 7.36/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_513,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | k1_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),X0) = k1_wellord1(X1,X0)
% 7.36/1.49      | sK7 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_514,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_513]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_38,negated_conjecture,
% 7.36/1.49      ( v1_relat_1(sK7) ),
% 7.36/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_517,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(sK7,X1))
% 7.36/1.49      | k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X1)),X0) = k1_wellord1(sK7,X0) ),
% 7.36/1.49      inference(global_propositional_subsumption,[status(thm)],[c_514,c_38]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2018,plain,
% 7.36/1.49      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),X1) = k1_wellord1(sK7,X1)
% 7.36/1.49      | r2_hidden(X1,k1_wellord1(sK7,X0)) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2670,plain,
% 7.36/1.49      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),X1)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),X1))
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,X0),X1) = iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2049,c_2018]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_6,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.36/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2045,plain,
% 7.36/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.36/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.36/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3603,plain,
% 7.36/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X2,X0)),X1) = iProver_top
% 7.36/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2027,c_2045]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_6570,plain,
% 7.36/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.36/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X3,X0)),X2) = iProver_top
% 7.36/1.49      | v1_relat_1(X3) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_3603,c_2045]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_11649,plain,
% 7.36/1.49      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),X1)) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),X1))
% 7.36/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X3,k1_wellord1(sK7,X0))),X2) = iProver_top
% 7.36/1.49      | v1_relat_1(X3) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2670,c_6570]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19379,plain,
% 7.36/1.49      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,X0)),sK0(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK5))) = k1_wellord1(sK7,sK0(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK5)))
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(k2_wellord1(X1,k1_wellord1(sK7,X0))),k1_wellord1(sK7,sK6)) = iProver_top
% 7.36/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2024,c_11649]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_39,plain,
% 7.36/1.49      ( v1_relat_1(sK7) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_40,plain,
% 7.36/1.49      ( v2_wellord1(sK7) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_36,negated_conjecture,
% 7.36/1.49      ( r2_hidden(sK5,k3_relat_1(sK7)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_41,plain,
% 7.36/1.49      ( r2_hidden(sK5,k3_relat_1(sK7)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_35,negated_conjecture,
% 7.36/1.49      ( r2_hidden(sK6,k3_relat_1(sK7)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_42,plain,
% 7.36/1.49      ( r2_hidden(sK6,k3_relat_1(sK7)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_43,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_18,plain,
% 7.36/1.49      ( v1_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_88,plain,
% 7.36/1.49      ( v1_relat_2(sK7) | ~ v2_wellord1(sK7) | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_87,plain,
% 7.36/1.49      ( v1_relat_2(X0) = iProver_top
% 7.36/1.49      | v2_wellord1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_89,plain,
% 7.36/1.49      ( v1_relat_2(sK7) = iProver_top
% 7.36/1.49      | v2_wellord1(sK7) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_87]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_15,plain,
% 7.36/1.49      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_96,plain,
% 7.36/1.49      ( v6_relat_2(X0) = iProver_top
% 7.36/1.49      | v2_wellord1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_98,plain,
% 7.36/1.49      ( v6_relat_2(sK7) = iProver_top
% 7.36/1.49      | v2_wellord1(sK7) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_96]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_121,plain,
% 7.36/1.49      ( r1_tarski(sK7,sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.36/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_125,plain,
% 7.36/1.49      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_12,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2108,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_wellord1(sK7,X0)) | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2248,plain,
% 7.36/1.49      ( ~ r2_hidden(sK6,k1_wellord1(sK7,sK6)) | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2108]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2251,plain,
% 7.36/1.49      ( r2_hidden(sK6,k1_wellord1(sK7,sK6)) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_2248]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2648,plain,
% 7.36/1.49      ( ~ r2_hidden(sK5,k1_wellord1(sK7,sK5)) | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2108]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_28,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.36/1.49      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.36/1.49      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.36/1.49      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.36/1.49      | ~ v6_relat_2(X1)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | X0 = X2 ),
% 7.36/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2289,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.36/1.49      | r2_hidden(k4_tarski(X0,sK6),X1)
% 7.36/1.49      | r2_hidden(k4_tarski(sK6,X0),X1)
% 7.36/1.49      | ~ r2_hidden(sK6,k3_relat_1(X1))
% 7.36/1.49      | ~ v6_relat_2(X1)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | X0 = sK6 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2853,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK6,sK5),sK7)
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | ~ r2_hidden(sK6,k3_relat_1(sK7))
% 7.36/1.49      | ~ r2_hidden(sK5,k3_relat_1(sK7))
% 7.36/1.49      | ~ v6_relat_2(sK7)
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | sK5 = sK6 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2289]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2854,plain,
% 7.36/1.49      ( sK5 = sK6
% 7.36/1.49      | r2_hidden(k4_tarski(sK6,sK5),sK7) = iProver_top
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top
% 7.36/1.49      | r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(sK5,k3_relat_1(sK7)) != iProver_top
% 7.36/1.49      | v6_relat_2(sK7) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_2853]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.36/1.49      | r2_hidden(k4_tarski(X0,X0),X1)
% 7.36/1.49      | ~ v1_relat_2(X1)
% 7.36/1.49      | ~ v1_relat_1(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3290,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.36/1.49      | ~ r2_hidden(sK6,k3_relat_1(sK7))
% 7.36/1.49      | ~ v1_relat_2(sK7)
% 7.36/1.49      | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3291,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK6,sK6),sK7) = iProver_top
% 7.36/1.49      | r2_hidden(sK6,k3_relat_1(sK7)) != iProver_top
% 7.36/1.49      | v1_relat_2(sK7) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_3290]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3293,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK5),sK7)
% 7.36/1.49      | ~ r2_hidden(sK5,k3_relat_1(sK7))
% 7.36/1.49      | ~ v1_relat_2(sK7)
% 7.36/1.49      | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_10,plain,
% 7.36/1.49      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.36/1.49      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | X0 = X2 ),
% 7.36/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2772,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK6,X0),X1)
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(X1,X0))
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | sK6 = X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4535,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK6,sK6),sK7)
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,sK6))
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | sK6 = sK6 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2772]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2789,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK5,X0),X1)
% 7.36/1.49      | r2_hidden(sK5,k1_wellord1(X1,X0))
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | sK5 = X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4552,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK5,sK5),sK7)
% 7.36/1.49      | r2_hidden(sK5,k1_wellord1(sK7,sK5))
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | sK5 = sK5 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2789]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.36/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2111,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1)
% 7.36/1.49      | r2_hidden(X0,k1_wellord1(sK7,X2))
% 7.36/1.49      | ~ r1_tarski(X1,k1_wellord1(sK7,X2)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2235,plain,
% 7.36/1.49      ( ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,X1))
% 7.36/1.49      | ~ r1_tarski(k1_wellord1(sK7,X0),k1_wellord1(sK7,X1)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2111]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2753,plain,
% 7.36/1.49      ( ~ r2_hidden(sK6,k1_wellord1(sK7,X0))
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,sK6))
% 7.36/1.49      | ~ r1_tarski(k1_wellord1(sK7,X0),k1_wellord1(sK7,sK6)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2235]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4848,plain,
% 7.36/1.49      ( r2_hidden(sK6,k1_wellord1(sK7,sK6))
% 7.36/1.49      | ~ r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.36/1.49      | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2753]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4849,plain,
% 7.36/1.49      ( r2_hidden(sK6,k1_wellord1(sK7,sK6)) = iProver_top
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,sK5)) != iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_4848]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2317,plain,
% 7.36/1.49      ( r2_hidden(X0,k1_wellord1(X1,sK5))
% 7.36/1.49      | ~ r2_hidden(k4_tarski(X0,sK5),X1)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | X0 = sK5 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4873,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK6,sK5),sK7)
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,sK5))
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | sK6 = sK5 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2317]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4874,plain,
% 7.36/1.49      ( sK6 = sK5
% 7.36/1.49      | r2_hidden(k4_tarski(sK6,sK5),sK7) != iProver_top
% 7.36/1.49      | r2_hidden(sK6,k1_wellord1(sK7,sK5)) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_4873]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1321,plain,
% 7.36/1.49      ( X0 != X1 | X2 != X3 | k4_tarski(X0,X2) = k4_tarski(X1,X3) ),
% 7.36/1.49      theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2439,plain,
% 7.36/1.49      ( k4_tarski(sK5,sK6) = k4_tarski(X0,X1) | sK6 != X1 | sK5 != X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1321]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2944,plain,
% 7.36/1.49      ( k4_tarski(sK5,sK6) = k4_tarski(X0,sK6) | sK6 != sK6 | sK5 != X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2439]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_8743,plain,
% 7.36/1.49      ( k4_tarski(sK5,sK6) = k4_tarski(sK6,sK6) | sK6 != sK6 | sK5 != sK6 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2944]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1317,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2799,plain,
% 7.36/1.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1317]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4387,plain,
% 7.36/1.49      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2799]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_8835,plain,
% 7.36/1.49      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_4387]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1319,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.36/1.49      theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2135,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1)
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | k4_tarski(sK5,sK6) != X0
% 7.36/1.49      | sK7 != X1 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1319]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2181,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | k4_tarski(sK5,sK6) != k4_tarski(X0,X1)
% 7.36/1.49      | sK7 != X2 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2135]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19322,plain,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK6,sK6),X0)
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
% 7.36/1.49      | sK7 != X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2181]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19323,plain,
% 7.36/1.49      ( k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
% 7.36/1.49      | sK7 != X0
% 7.36/1.49      | r2_hidden(k4_tarski(sK6,sK6),X0) != iProver_top
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_19322]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19325,plain,
% 7.36/1.49      ( k4_tarski(sK5,sK6) != k4_tarski(sK6,sK6)
% 7.36/1.49      | sK7 != sK7
% 7.36/1.49      | r2_hidden(k4_tarski(sK6,sK6),sK7) != iProver_top
% 7.36/1.49      | r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_19323]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19464,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7) = iProver_top ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_19379,c_38,c_39,c_37,c_40,c_36,c_41,c_35,c_42,c_43,c_88,
% 7.36/1.49                 c_89,c_98,c_121,c_125,c_2248,c_2251,c_2648,c_2854,c_3290,
% 7.36/1.49                 c_3291,c_3293,c_4535,c_4552,c_4849,c_4874,c_8743,c_8835,
% 7.36/1.49                 c_19325]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2041,plain,
% 7.36/1.49      ( X0 = X1
% 7.36/1.49      | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
% 7.36/1.49      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 7.36/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19469,plain,
% 7.36/1.49      ( sK6 = sK5
% 7.36/1.49      | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_19464,c_2041]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19627,plain,
% 7.36/1.49      ( r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top | sK6 = sK5 ),
% 7.36/1.49      inference(global_propositional_subsumption,[status(thm)],[c_19469,c_39]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19628,plain,
% 7.36/1.49      ( sK6 = sK5 | r2_hidden(sK5,k1_wellord1(sK7,sK6)) = iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_19627]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19633,plain,
% 7.36/1.49      ( k1_wellord1(k2_wellord1(sK7,k1_wellord1(sK7,sK6)),sK5) = k1_wellord1(sK7,sK5)
% 7.36/1.49      | sK6 = sK5 ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_19628,c_2018]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_29,plain,
% 7.36/1.49      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2028,plain,
% 7.36/1.49      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) = iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3602,plain,
% 7.36/1.49      ( r1_tarski(k1_wellord1(X0,X1),X2) = iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(X0),X2) != iProver_top
% 7.36/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2028,c_2045]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_19968,plain,
% 7.36/1.49      ( sK6 = sK5
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),X0) = iProver_top
% 7.36/1.49      | r1_tarski(k3_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))),X0) != iProver_top
% 7.36/1.49      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_19633,c_3602]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_21971,plain,
% 7.36/1.49      ( sK6 = sK5
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) = iProver_top
% 7.36/1.49      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2027,c_19968]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_33,negated_conjecture,
% 7.36/1.49      ( ~ r2_hidden(k4_tarski(sK5,sK6),sK7)
% 7.36/1.49      | ~ r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_44,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22100,plain,
% 7.36/1.49      ( v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top
% 7.36/1.49      | sK6 = sK5 ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_21971,c_38,c_39,c_37,c_40,c_36,c_41,c_35,c_42,c_43,c_44,
% 7.36/1.49                 c_88,c_89,c_98,c_121,c_125,c_2248,c_2251,c_2648,c_2854,
% 7.36/1.49                 c_3290,c_3291,c_3293,c_4535,c_4552,c_4849,c_4874,c_8743,
% 7.36/1.49                 c_8835,c_19325]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22101,plain,
% 7.36/1.49      ( sK6 = sK5
% 7.36/1.49      | v1_relat_1(k2_wellord1(sK7,k1_wellord1(sK7,sK6))) != iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_22100]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22104,plain,
% 7.36/1.49      ( sK6 = sK5 | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2038,c_22101]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22107,plain,
% 7.36/1.49      ( sK6 = sK5 ),
% 7.36/1.49      inference(global_propositional_subsumption,[status(thm)],[c_22104,c_39]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2025,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK6),sK7) != iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK6)) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22125,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK5),sK7) != iProver_top
% 7.36/1.49      | r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
% 7.36/1.49      inference(demodulation,[status(thm)],[c_22107,c_2025]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3294,plain,
% 7.36/1.49      ( r2_hidden(k4_tarski(sK5,sK5),sK7) = iProver_top
% 7.36/1.50      | r2_hidden(sK5,k3_relat_1(sK7)) != iProver_top
% 7.36/1.50      | v1_relat_2(sK7) != iProver_top
% 7.36/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.50      inference(predicate_to_equality,[status(thm)],[c_3293]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_22285,plain,
% 7.36/1.50      ( r1_tarski(k1_wellord1(sK7,sK5),k1_wellord1(sK7,sK5)) != iProver_top ),
% 7.36/1.50      inference(global_propositional_subsumption,
% 7.36/1.50                [status(thm)],
% 7.36/1.50                [c_22125,c_39,c_40,c_41,c_89,c_3294]) ).
% 7.36/1.50  
% 7.36/1.50  cnf(c_22289,plain,
% 7.36/1.50      ( $false ),
% 7.36/1.50      inference(superposition,[status(thm)],[c_2046,c_22285]) ).
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.50  
% 7.36/1.50  ------                               Statistics
% 7.36/1.50  
% 7.36/1.50  ------ General
% 7.36/1.50  
% 7.36/1.50  abstr_ref_over_cycles:                  0
% 7.36/1.50  abstr_ref_under_cycles:                 0
% 7.36/1.50  gc_basic_clause_elim:                   0
% 7.36/1.50  forced_gc_time:                         0
% 7.36/1.50  parsing_time:                           0.006
% 7.36/1.50  unif_index_cands_time:                  0.
% 7.36/1.50  unif_index_add_time:                    0.
% 7.36/1.50  orderings_time:                         0.
% 7.36/1.50  out_proof_time:                         0.012
% 7.36/1.50  total_time:                             0.683
% 7.36/1.50  num_of_symbols:                         52
% 7.36/1.50  num_of_terms:                           24834
% 7.36/1.50  
% 7.36/1.50  ------ Preprocessing
% 7.36/1.50  
% 7.36/1.50  num_of_splits:                          0
% 7.36/1.50  num_of_split_atoms:                     0
% 7.36/1.50  num_of_reused_defs:                     0
% 7.36/1.50  num_eq_ax_congr_red:                    30
% 7.36/1.50  num_of_sem_filtered_clauses:            1
% 7.36/1.50  num_of_subtypes:                        0
% 7.36/1.50  monotx_restored_types:                  0
% 7.36/1.50  sat_num_of_epr_types:                   0
% 7.36/1.50  sat_num_of_non_cyclic_types:            0
% 7.36/1.50  sat_guarded_non_collapsed_types:        0
% 7.36/1.50  num_pure_diseq_elim:                    0
% 7.36/1.50  simp_replaced_by:                       0
% 7.36/1.50  res_preprocessed:                       160
% 7.36/1.50  prep_upred:                             0
% 7.36/1.50  prep_unflattend:                        21
% 7.36/1.50  smt_new_axioms:                         0
% 7.36/1.50  pred_elim_cands:                        5
% 7.36/1.50  pred_elim:                              4
% 7.36/1.50  pred_elim_cl:                           5
% 7.36/1.50  pred_elim_cycles:                       8
% 7.36/1.50  merged_defs:                            8
% 7.36/1.50  merged_defs_ncl:                        0
% 7.36/1.50  bin_hyper_res:                          8
% 7.36/1.50  prep_cycles:                            4
% 7.36/1.50  pred_elim_time:                         0.005
% 7.36/1.50  splitting_time:                         0.
% 7.36/1.50  sem_filter_time:                        0.
% 7.36/1.50  monotx_time:                            0.
% 7.36/1.50  subtype_inf_time:                       0.
% 7.36/1.50  
% 7.36/1.50  ------ Problem properties
% 7.36/1.50  
% 7.36/1.50  clauses:                                33
% 7.36/1.50  conjectures:                            5
% 7.36/1.50  epr:                                    7
% 7.36/1.50  horn:                                   23
% 7.36/1.50  ground:                                 7
% 7.36/1.50  unary:                                  6
% 7.36/1.50  binary:                                 10
% 7.36/1.50  lits:                                   87
% 7.36/1.50  lits_eq:                                10
% 7.36/1.50  fd_pure:                                0
% 7.36/1.50  fd_pseudo:                              0
% 7.36/1.50  fd_cond:                                0
% 7.36/1.50  fd_pseudo_cond:                         5
% 7.36/1.50  ac_symbols:                             0
% 7.36/1.50  
% 7.36/1.50  ------ Propositional Solver
% 7.36/1.50  
% 7.36/1.50  prop_solver_calls:                      30
% 7.36/1.50  prop_fast_solver_calls:                 1825
% 7.36/1.50  smt_solver_calls:                       0
% 7.36/1.50  smt_fast_solver_calls:                  0
% 7.36/1.50  prop_num_of_clauses:                    9937
% 7.36/1.50  prop_preprocess_simplified:             18104
% 7.36/1.50  prop_fo_subsumed:                       54
% 7.36/1.50  prop_solver_time:                       0.
% 7.36/1.50  smt_solver_time:                        0.
% 7.36/1.50  smt_fast_solver_time:                   0.
% 7.36/1.50  prop_fast_solver_time:                  0.
% 7.36/1.50  prop_unsat_core_time:                   0.
% 7.36/1.50  
% 7.36/1.50  ------ QBF
% 7.36/1.50  
% 7.36/1.50  qbf_q_res:                              0
% 7.36/1.50  qbf_num_tautologies:                    0
% 7.36/1.50  qbf_prep_cycles:                        0
% 7.36/1.50  
% 7.36/1.50  ------ BMC1
% 7.36/1.50  
% 7.36/1.50  bmc1_current_bound:                     -1
% 7.36/1.50  bmc1_last_solved_bound:                 -1
% 7.36/1.50  bmc1_unsat_core_size:                   -1
% 7.36/1.50  bmc1_unsat_core_parents_size:           -1
% 7.36/1.50  bmc1_merge_next_fun:                    0
% 7.36/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.50  
% 7.36/1.50  ------ Instantiation
% 7.36/1.50  
% 7.36/1.50  inst_num_of_clauses:                    1821
% 7.36/1.50  inst_num_in_passive:                    859
% 7.36/1.50  inst_num_in_active:                     642
% 7.36/1.50  inst_num_in_unprocessed:                320
% 7.36/1.50  inst_num_of_loops:                      950
% 7.36/1.50  inst_num_of_learning_restarts:          0
% 7.36/1.50  inst_num_moves_active_passive:          306
% 7.36/1.50  inst_lit_activity:                      0
% 7.36/1.50  inst_lit_activity_moves:                0
% 7.36/1.50  inst_num_tautologies:                   0
% 7.36/1.50  inst_num_prop_implied:                  0
% 7.36/1.50  inst_num_existing_simplified:           0
% 7.36/1.50  inst_num_eq_res_simplified:             0
% 7.36/1.50  inst_num_child_elim:                    0
% 7.36/1.50  inst_num_of_dismatching_blockings:      1396
% 7.36/1.50  inst_num_of_non_proper_insts:           2501
% 7.36/1.50  inst_num_of_duplicates:                 0
% 7.36/1.50  inst_inst_num_from_inst_to_res:         0
% 7.36/1.50  inst_dismatching_checking_time:         0.
% 7.36/1.50  
% 7.36/1.50  ------ Resolution
% 7.36/1.50  
% 7.36/1.50  res_num_of_clauses:                     0
% 7.36/1.50  res_num_in_passive:                     0
% 7.36/1.50  res_num_in_active:                      0
% 7.36/1.50  res_num_of_loops:                       164
% 7.36/1.50  res_forward_subset_subsumed:            84
% 7.36/1.50  res_backward_subset_subsumed:           0
% 7.36/1.50  res_forward_subsumed:                   0
% 7.36/1.50  res_backward_subsumed:                  0
% 7.36/1.50  res_forward_subsumption_resolution:     0
% 7.36/1.50  res_backward_subsumption_resolution:    0
% 7.36/1.50  res_clause_to_clause_subsumption:       6685
% 7.36/1.50  res_orphan_elimination:                 0
% 7.36/1.50  res_tautology_del:                      221
% 7.36/1.50  res_num_eq_res_simplified:              0
% 7.36/1.50  res_num_sel_changes:                    0
% 7.36/1.50  res_moves_from_active_to_pass:          0
% 7.36/1.50  
% 7.36/1.50  ------ Superposition
% 7.36/1.50  
% 7.36/1.50  sup_time_total:                         0.
% 7.36/1.50  sup_time_generating:                    0.
% 7.36/1.50  sup_time_sim_full:                      0.
% 7.36/1.50  sup_time_sim_immed:                     0.
% 7.36/1.50  
% 7.36/1.50  sup_num_of_clauses:                     1074
% 7.36/1.50  sup_num_in_active:                      93
% 7.36/1.50  sup_num_in_passive:                     981
% 7.36/1.50  sup_num_of_loops:                       188
% 7.36/1.50  sup_fw_superposition:                   789
% 7.36/1.50  sup_bw_superposition:                   688
% 7.36/1.50  sup_immediate_simplified:               104
% 7.36/1.50  sup_given_eliminated:                   0
% 7.36/1.50  comparisons_done:                       0
% 7.36/1.50  comparisons_avoided:                    182
% 7.36/1.50  
% 7.36/1.50  ------ Simplifications
% 7.36/1.50  
% 7.36/1.50  
% 7.36/1.50  sim_fw_subset_subsumed:                 33
% 7.36/1.50  sim_bw_subset_subsumed:                 56
% 7.36/1.50  sim_fw_subsumed:                        45
% 7.36/1.50  sim_bw_subsumed:                        76
% 7.36/1.50  sim_fw_subsumption_res:                 0
% 7.36/1.50  sim_bw_subsumption_res:                 0
% 7.36/1.50  sim_tautology_del:                      35
% 7.36/1.50  sim_eq_tautology_del:                   50
% 7.36/1.50  sim_eq_res_simp:                        0
% 7.36/1.50  sim_fw_demodulated:                     3
% 7.36/1.50  sim_bw_demodulated:                     23
% 7.36/1.50  sim_light_normalised:                   4
% 7.36/1.50  sim_joinable_taut:                      0
% 7.36/1.50  sim_joinable_simp:                      0
% 7.36/1.50  sim_ac_normalised:                      0
% 7.36/1.50  sim_smt_subsumption:                    0
% 7.36/1.50  
%------------------------------------------------------------------------------
