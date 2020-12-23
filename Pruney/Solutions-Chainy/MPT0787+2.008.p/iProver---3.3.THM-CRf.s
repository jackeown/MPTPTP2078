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
% DateTime   : Thu Dec  3 11:54:32 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 896 expanded)
%              Number of clauses        :   92 ( 228 expanded)
%              Number of leaves         :   16 ( 156 expanded)
%              Depth                    :   25
%              Number of atoms          :  773 (5667 expanded)
%              Number of equality atoms :  182 ( 707 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
        | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) )
      & ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
        | r2_hidden(k4_tarski(sK8,sK9),sK10) )
      & r2_hidden(sK9,k3_relat_1(sK10))
      & r2_hidden(sK8,k3_relat_1(sK10))
      & v2_wellord1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
      | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) )
    & ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
      | r2_hidden(k4_tarski(sK8,sK9),sK10) )
    & r2_hidden(sK9,k3_relat_1(sK10))
    & r2_hidden(sK8,k3_relat_1(sK10))
    & v2_wellord1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f48,f49])).

fof(f88,plain,
    ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f15,plain,(
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

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).

fof(f69,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    v2_wellord1(sK10) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f12])).

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
    inference(flattening,[],[f25])).

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
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f50])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f93,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f87,plain,(
    r2_hidden(sK9,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,
    ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(cnf_transformation,[],[f50])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X0) )
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X4,X0)
                  & r2_hidden(k4_tarski(X4,X3),X1) )
              & r2_hidden(X3,X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X3),X1) )
     => ( ~ r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1),X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,X0)
              & r2_hidden(k4_tarski(X4,X3),X1) )
          & r2_hidden(X3,X0) )
     => ( ? [X4] :
            ( ~ r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,sK6(X0,X1)),X1) )
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X1,X2) = X0
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK5(X0,X1)) = X0
        & r2_hidden(sK5(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X1,sK5(X0,X1)) = X0
            & r2_hidden(sK5(X0,X1),k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ( ~ r2_hidden(sK7(X0,X1),X0)
            & r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X1)
            & r2_hidden(sK6(X0,X1),X0) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r2_hidden(X6,X0)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1) )
              | ~ r2_hidden(X5,X0) )
          | ( ! [X7] :
                ( k1_wellord1(X1,X7) != X0
                | ~ r2_hidden(X7,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).

fof(f77,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k1_wellord1(X1,X7) != X0
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X6,X7,X5,X1] :
      ( r2_hidden(X6,k1_wellord1(X1,X7))
      | ~ r2_hidden(k4_tarski(X6,X5),X1)
      | ~ r2_hidden(X5,k1_wellord1(X1,X7))
      | ~ r2_hidden(X7,k3_relat_1(X1))
      | ~ r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3541,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_952,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v6_relat_2(X1)
    | X2 = X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_953,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X1,X0),sK10)
    | r2_hidden(k4_tarski(X0,X1),sK10)
    | ~ v6_relat_2(sK10)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_37,negated_conjecture,
    ( v2_wellord1(sK10) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11,plain,
    ( v6_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_105,plain,
    ( v6_relat_2(sK10)
    | ~ v2_wellord1(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_955,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK10)
    | r2_hidden(k4_tarski(X1,X0),sK10)
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | ~ r2_hidden(X0,k3_relat_1(sK10))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_38,c_37,c_105])).

cnf(c_956,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X1,X0),sK10)
    | r2_hidden(k4_tarski(X0,X1),sK10)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_955])).

cnf(c_3527,plain,
    ( X0 = X1
    | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK10) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1008,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | X2 = X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_38])).

cnf(c_1009,plain,
    ( r2_hidden(X0,k1_wellord1(sK10,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK10)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1008])).

cnf(c_3524,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK10,X0)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_5611,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3527,c_3524])).

cnf(c_9796,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_wellord1(sK10,X0)) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5611,c_3524])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3543,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10805,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
    | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r1_tarski(k1_wellord1(sK10,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9796,c_3543])).

cnf(c_24574,plain,
    ( sK8 = X0
    | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top
    | r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3541,c_10805])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,plain,
    ( r2_hidden(sK8,k3_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_24879,plain,
    ( r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
    | sK8 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24574,c_41])).

cnf(c_24880,plain,
    ( sK8 = X0
    | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_24879])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_989,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_38])).

cnf(c_990,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,X0)) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_3526,plain,
    ( r2_hidden(X0,k1_wellord1(sK10,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_24903,plain,
    ( sK9 = sK8
    | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24880,c_3526])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK9,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( r2_hidden(sK9,k3_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_298,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_1085,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r2_hidden(sK0(X0,X1),X0)
    | k1_wellord1(sK10,sK9) != X1
    | k1_wellord1(sK10,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_298])).

cnf(c_1086,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) ),
    inference(unflattening,[status(thm)],[c_1085])).

cnf(c_1087,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1095,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_wellord1(sK10,sK9) != X1
    | k1_wellord1(sK10,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_298])).

cnf(c_1096,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1097,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_3902,plain,
    ( ~ r2_hidden(k4_tarski(sK8,X0),sK10)
    | r2_hidden(sK8,k1_wellord1(sK10,X0))
    | X0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_4563,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r2_hidden(sK8,k1_wellord1(sK10,sK9))
    | sK9 = sK8 ),
    inference(instantiation,[status(thm)],[c_3902])).

cnf(c_4564,plain,
    ( sK9 = sK8
    | r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4563])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_998,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_38])).

cnf(c_999,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
    | r2_hidden(k4_tarski(X0,X1),sK10) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_6432,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10)
    | ~ r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_6433,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10) = iProver_top
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6432])).

cnf(c_4064,plain,
    ( r2_hidden(k4_tarski(sK8,X0),sK10)
    | ~ r2_hidden(sK8,k1_wellord1(sK10,X0)) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_7544,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_4064])).

cnf(c_7545,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7544])).

cnf(c_24,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_881,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_882,plain,
    ( r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10)) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(X3,k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X3,X0),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_610,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
    | r2_hidden(X2,k1_wellord1(sK10,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(X2,X0),sK10)
    | ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10))
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(X2,X0),sK10)
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | r2_hidden(X2,k1_wellord1(sK10,X1))
    | ~ r2_hidden(X0,k1_wellord1(sK10,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_38])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
    | r2_hidden(X2,k1_wellord1(sK10,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(X2,X0),sK10)
    | ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10)) ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_1027,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
    | r2_hidden(X2,k1_wellord1(sK10,X1))
    | ~ r2_hidden(X1,k3_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(X2,X0),sK10) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_882,c_613])).

cnf(c_3760,plain,
    ( ~ r2_hidden(X0,k1_wellord1(sK10,sK9))
    | r2_hidden(X1,k1_wellord1(sK10,sK9))
    | ~ r2_hidden(k4_tarski(X1,X0),sK10)
    | ~ r2_hidden(sK9,k3_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_4253,plain,
    ( r2_hidden(X0,k1_wellord1(sK10,sK9))
    | ~ r2_hidden(k4_tarski(X0,sK8),sK10)
    | ~ r2_hidden(sK9,k3_relat_1(sK10))
    | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_3760])).

cnf(c_24542,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10)
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9))
    | ~ r2_hidden(sK9,k3_relat_1(sK10))
    | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_4253])).

cnf(c_24543,plain,
    ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10) != iProver_top
    | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) = iProver_top
    | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24542])).

cnf(c_25149,plain,
    ( sK9 = sK8
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24903,c_42,c_1087,c_1097,c_4564,c_6433,c_7545,c_24543])).

cnf(c_25153,plain,
    ( sK9 = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25149,c_42,c_1087,c_1097,c_4564,c_6433,c_7545,c_24543,c_24903])).

cnf(c_3542,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_25181,plain,
    ( r2_hidden(k4_tarski(sK8,sK8),sK10) != iProver_top
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25153,c_3542])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_975,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_976,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X0,X0),sK10)
    | ~ v1_relat_2(sK10) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_14,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_567,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_37])).

cnf(c_568,plain,
    ( v1_relat_2(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_96,plain,
    ( v1_relat_2(sK10)
    | ~ v2_wellord1(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_570,plain,
    ( v1_relat_2(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_38,c_37,c_96])).

cnf(c_853,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_1(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_570])).

cnf(c_854,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X0,X0),sK10)
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK10)
    | ~ r2_hidden(X0,k3_relat_1(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_38])).

cnf(c_859,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X0,X0),sK10) ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_978,plain,
    ( r2_hidden(k4_tarski(X0,X0),sK10)
    | ~ r2_hidden(X0,k3_relat_1(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_38,c_854])).

cnf(c_979,plain,
    ( ~ r2_hidden(X0,k3_relat_1(sK10))
    | r2_hidden(k4_tarski(X0,X0),sK10) ),
    inference(renaming,[status(thm)],[c_978])).

cnf(c_3735,plain,
    ( r2_hidden(k4_tarski(sK8,sK8),sK10)
    | ~ r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_3736,plain,
    ( r2_hidden(k4_tarski(sK8,sK8),sK10) = iProver_top
    | r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3735])).

cnf(c_25307,plain,
    ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25181,c_41,c_3736])).

cnf(c_3544,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3545,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4096,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_3545])).

cnf(c_25312,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25307,c_4096])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.64/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.50  
% 7.64/1.50  ------  iProver source info
% 7.64/1.50  
% 7.64/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.50  git: non_committed_changes: false
% 7.64/1.50  git: last_make_outside_of_git: false
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options
% 7.64/1.50  
% 7.64/1.50  --out_options                           all
% 7.64/1.50  --tptp_safe_out                         true
% 7.64/1.50  --problem_path                          ""
% 7.64/1.50  --include_path                          ""
% 7.64/1.50  --clausifier                            res/vclausify_rel
% 7.64/1.50  --clausifier_options                    --mode clausify
% 7.64/1.50  --stdin                                 false
% 7.64/1.50  --stats_out                             all
% 7.64/1.50  
% 7.64/1.50  ------ General Options
% 7.64/1.50  
% 7.64/1.50  --fof                                   false
% 7.64/1.50  --time_out_real                         305.
% 7.64/1.50  --time_out_virtual                      -1.
% 7.64/1.50  --symbol_type_check                     false
% 7.64/1.50  --clausify_out                          false
% 7.64/1.50  --sig_cnt_out                           false
% 7.64/1.50  --trig_cnt_out                          false
% 7.64/1.50  --trig_cnt_out_tolerance                1.
% 7.64/1.50  --trig_cnt_out_sk_spl                   false
% 7.64/1.50  --abstr_cl_out                          false
% 7.64/1.50  
% 7.64/1.50  ------ Global Options
% 7.64/1.50  
% 7.64/1.50  --schedule                              default
% 7.64/1.50  --add_important_lit                     false
% 7.64/1.50  --prop_solver_per_cl                    1000
% 7.64/1.50  --min_unsat_core                        false
% 7.64/1.50  --soft_assumptions                      false
% 7.64/1.50  --soft_lemma_size                       3
% 7.64/1.50  --prop_impl_unit_size                   0
% 7.64/1.50  --prop_impl_unit                        []
% 7.64/1.50  --share_sel_clauses                     true
% 7.64/1.50  --reset_solvers                         false
% 7.64/1.50  --bc_imp_inh                            [conj_cone]
% 7.64/1.50  --conj_cone_tolerance                   3.
% 7.64/1.50  --extra_neg_conj                        none
% 7.64/1.50  --large_theory_mode                     true
% 7.64/1.50  --prolific_symb_bound                   200
% 7.64/1.50  --lt_threshold                          2000
% 7.64/1.50  --clause_weak_htbl                      true
% 7.64/1.50  --gc_record_bc_elim                     false
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing Options
% 7.64/1.50  
% 7.64/1.50  --preprocessing_flag                    true
% 7.64/1.50  --time_out_prep_mult                    0.1
% 7.64/1.50  --splitting_mode                        input
% 7.64/1.50  --splitting_grd                         true
% 7.64/1.50  --splitting_cvd                         false
% 7.64/1.50  --splitting_cvd_svl                     false
% 7.64/1.50  --splitting_nvd                         32
% 7.64/1.50  --sub_typing                            true
% 7.64/1.50  --prep_gs_sim                           true
% 7.64/1.50  --prep_unflatten                        true
% 7.64/1.50  --prep_res_sim                          true
% 7.64/1.50  --prep_upred                            true
% 7.64/1.50  --prep_sem_filter                       exhaustive
% 7.64/1.50  --prep_sem_filter_out                   false
% 7.64/1.50  --pred_elim                             true
% 7.64/1.50  --res_sim_input                         true
% 7.64/1.50  --eq_ax_congr_red                       true
% 7.64/1.50  --pure_diseq_elim                       true
% 7.64/1.50  --brand_transform                       false
% 7.64/1.50  --non_eq_to_eq                          false
% 7.64/1.50  --prep_def_merge                        true
% 7.64/1.50  --prep_def_merge_prop_impl              false
% 7.64/1.50  --prep_def_merge_mbd                    true
% 7.64/1.50  --prep_def_merge_tr_red                 false
% 7.64/1.50  --prep_def_merge_tr_cl                  false
% 7.64/1.50  --smt_preprocessing                     true
% 7.64/1.50  --smt_ac_axioms                         fast
% 7.64/1.50  --preprocessed_out                      false
% 7.64/1.50  --preprocessed_stats                    false
% 7.64/1.50  
% 7.64/1.50  ------ Abstraction refinement Options
% 7.64/1.50  
% 7.64/1.50  --abstr_ref                             []
% 7.64/1.50  --abstr_ref_prep                        false
% 7.64/1.50  --abstr_ref_until_sat                   false
% 7.64/1.50  --abstr_ref_sig_restrict                funpre
% 7.64/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.50  --abstr_ref_under                       []
% 7.64/1.50  
% 7.64/1.50  ------ SAT Options
% 7.64/1.50  
% 7.64/1.50  --sat_mode                              false
% 7.64/1.50  --sat_fm_restart_options                ""
% 7.64/1.50  --sat_gr_def                            false
% 7.64/1.50  --sat_epr_types                         true
% 7.64/1.50  --sat_non_cyclic_types                  false
% 7.64/1.50  --sat_finite_models                     false
% 7.64/1.50  --sat_fm_lemmas                         false
% 7.64/1.50  --sat_fm_prep                           false
% 7.64/1.50  --sat_fm_uc_incr                        true
% 7.64/1.50  --sat_out_model                         small
% 7.64/1.50  --sat_out_clauses                       false
% 7.64/1.50  
% 7.64/1.50  ------ QBF Options
% 7.64/1.50  
% 7.64/1.50  --qbf_mode                              false
% 7.64/1.50  --qbf_elim_univ                         false
% 7.64/1.50  --qbf_dom_inst                          none
% 7.64/1.50  --qbf_dom_pre_inst                      false
% 7.64/1.50  --qbf_sk_in                             false
% 7.64/1.50  --qbf_pred_elim                         true
% 7.64/1.50  --qbf_split                             512
% 7.64/1.50  
% 7.64/1.50  ------ BMC1 Options
% 7.64/1.50  
% 7.64/1.50  --bmc1_incremental                      false
% 7.64/1.50  --bmc1_axioms                           reachable_all
% 7.64/1.50  --bmc1_min_bound                        0
% 7.64/1.50  --bmc1_max_bound                        -1
% 7.64/1.50  --bmc1_max_bound_default                -1
% 7.64/1.50  --bmc1_symbol_reachability              true
% 7.64/1.50  --bmc1_property_lemmas                  false
% 7.64/1.50  --bmc1_k_induction                      false
% 7.64/1.50  --bmc1_non_equiv_states                 false
% 7.64/1.50  --bmc1_deadlock                         false
% 7.64/1.50  --bmc1_ucm                              false
% 7.64/1.50  --bmc1_add_unsat_core                   none
% 7.64/1.50  --bmc1_unsat_core_children              false
% 7.64/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.50  --bmc1_out_stat                         full
% 7.64/1.50  --bmc1_ground_init                      false
% 7.64/1.50  --bmc1_pre_inst_next_state              false
% 7.64/1.50  --bmc1_pre_inst_state                   false
% 7.64/1.50  --bmc1_pre_inst_reach_state             false
% 7.64/1.50  --bmc1_out_unsat_core                   false
% 7.64/1.50  --bmc1_aig_witness_out                  false
% 7.64/1.50  --bmc1_verbose                          false
% 7.64/1.50  --bmc1_dump_clauses_tptp                false
% 7.64/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.50  --bmc1_dump_file                        -
% 7.64/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.50  --bmc1_ucm_extend_mode                  1
% 7.64/1.50  --bmc1_ucm_init_mode                    2
% 7.64/1.50  --bmc1_ucm_cone_mode                    none
% 7.64/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.50  --bmc1_ucm_relax_model                  4
% 7.64/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.50  --bmc1_ucm_layered_model                none
% 7.64/1.50  --bmc1_ucm_max_lemma_size               10
% 7.64/1.50  
% 7.64/1.50  ------ AIG Options
% 7.64/1.50  
% 7.64/1.50  --aig_mode                              false
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation Options
% 7.64/1.50  
% 7.64/1.50  --instantiation_flag                    true
% 7.64/1.50  --inst_sos_flag                         false
% 7.64/1.50  --inst_sos_phase                        true
% 7.64/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel_side                     num_symb
% 7.64/1.50  --inst_solver_per_active                1400
% 7.64/1.50  --inst_solver_calls_frac                1.
% 7.64/1.50  --inst_passive_queue_type               priority_queues
% 7.64/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.50  --inst_passive_queues_freq              [25;2]
% 7.64/1.50  --inst_dismatching                      true
% 7.64/1.50  --inst_eager_unprocessed_to_passive     true
% 7.64/1.50  --inst_prop_sim_given                   true
% 7.64/1.50  --inst_prop_sim_new                     false
% 7.64/1.50  --inst_subs_new                         false
% 7.64/1.50  --inst_eq_res_simp                      false
% 7.64/1.50  --inst_subs_given                       false
% 7.64/1.50  --inst_orphan_elimination               true
% 7.64/1.50  --inst_learning_loop_flag               true
% 7.64/1.50  --inst_learning_start                   3000
% 7.64/1.50  --inst_learning_factor                  2
% 7.64/1.50  --inst_start_prop_sim_after_learn       3
% 7.64/1.50  --inst_sel_renew                        solver
% 7.64/1.50  --inst_lit_activity_flag                true
% 7.64/1.50  --inst_restr_to_given                   false
% 7.64/1.50  --inst_activity_threshold               500
% 7.64/1.50  --inst_out_proof                        true
% 7.64/1.50  
% 7.64/1.50  ------ Resolution Options
% 7.64/1.50  
% 7.64/1.50  --resolution_flag                       true
% 7.64/1.50  --res_lit_sel                           adaptive
% 7.64/1.50  --res_lit_sel_side                      none
% 7.64/1.50  --res_ordering                          kbo
% 7.64/1.50  --res_to_prop_solver                    active
% 7.64/1.50  --res_prop_simpl_new                    false
% 7.64/1.50  --res_prop_simpl_given                  true
% 7.64/1.50  --res_passive_queue_type                priority_queues
% 7.64/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.50  --res_passive_queues_freq               [15;5]
% 7.64/1.50  --res_forward_subs                      full
% 7.64/1.50  --res_backward_subs                     full
% 7.64/1.50  --res_forward_subs_resolution           true
% 7.64/1.50  --res_backward_subs_resolution          true
% 7.64/1.50  --res_orphan_elimination                true
% 7.64/1.50  --res_time_limit                        2.
% 7.64/1.50  --res_out_proof                         true
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Options
% 7.64/1.50  
% 7.64/1.50  --superposition_flag                    true
% 7.64/1.50  --sup_passive_queue_type                priority_queues
% 7.64/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.50  --demod_completeness_check              fast
% 7.64/1.50  --demod_use_ground                      true
% 7.64/1.50  --sup_to_prop_solver                    passive
% 7.64/1.50  --sup_prop_simpl_new                    true
% 7.64/1.50  --sup_prop_simpl_given                  true
% 7.64/1.50  --sup_fun_splitting                     false
% 7.64/1.50  --sup_smt_interval                      50000
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Simplification Setup
% 7.64/1.50  
% 7.64/1.50  --sup_indices_passive                   []
% 7.64/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_full_bw                           [BwDemod]
% 7.64/1.50  --sup_immed_triv                        [TrivRules]
% 7.64/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_immed_bw_main                     []
% 7.64/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.50  
% 7.64/1.50  ------ Combination Options
% 7.64/1.50  
% 7.64/1.50  --comb_res_mult                         3
% 7.64/1.50  --comb_sup_mult                         2
% 7.64/1.50  --comb_inst_mult                        10
% 7.64/1.50  
% 7.64/1.50  ------ Debug Options
% 7.64/1.50  
% 7.64/1.50  --dbg_backtrace                         false
% 7.64/1.50  --dbg_dump_prop_clauses                 false
% 7.64/1.50  --dbg_dump_prop_clauses_file            -
% 7.64/1.50  --dbg_out_stat                          false
% 7.64/1.50  ------ Parsing...
% 7.64/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.50  ------ Proving...
% 7.64/1.50  ------ Problem Properties 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  clauses                                 24
% 7.64/1.50  conjectures                             4
% 7.64/1.50  EPR                                     1
% 7.64/1.50  Horn                                    11
% 7.64/1.50  unary                                   4
% 7.64/1.50  binary                                  6
% 7.64/1.50  lits                                    68
% 7.64/1.50  lits eq                                 16
% 7.64/1.50  fd_pure                                 0
% 7.64/1.50  fd_pseudo                               0
% 7.64/1.50  fd_cond                                 3
% 7.64/1.50  fd_pseudo_cond                          4
% 7.64/1.50  AC symbols                              0
% 7.64/1.50  
% 7.64/1.50  ------ Schedule dynamic 5 is on 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  Current options:
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options
% 7.64/1.50  
% 7.64/1.50  --out_options                           all
% 7.64/1.50  --tptp_safe_out                         true
% 7.64/1.50  --problem_path                          ""
% 7.64/1.50  --include_path                          ""
% 7.64/1.50  --clausifier                            res/vclausify_rel
% 7.64/1.50  --clausifier_options                    --mode clausify
% 7.64/1.50  --stdin                                 false
% 7.64/1.50  --stats_out                             all
% 7.64/1.50  
% 7.64/1.50  ------ General Options
% 7.64/1.50  
% 7.64/1.50  --fof                                   false
% 7.64/1.50  --time_out_real                         305.
% 7.64/1.50  --time_out_virtual                      -1.
% 7.64/1.50  --symbol_type_check                     false
% 7.64/1.50  --clausify_out                          false
% 7.64/1.50  --sig_cnt_out                           false
% 7.64/1.50  --trig_cnt_out                          false
% 7.64/1.50  --trig_cnt_out_tolerance                1.
% 7.64/1.50  --trig_cnt_out_sk_spl                   false
% 7.64/1.50  --abstr_cl_out                          false
% 7.64/1.50  
% 7.64/1.50  ------ Global Options
% 7.64/1.50  
% 7.64/1.50  --schedule                              default
% 7.64/1.50  --add_important_lit                     false
% 7.64/1.50  --prop_solver_per_cl                    1000
% 7.64/1.50  --min_unsat_core                        false
% 7.64/1.50  --soft_assumptions                      false
% 7.64/1.50  --soft_lemma_size                       3
% 7.64/1.50  --prop_impl_unit_size                   0
% 7.64/1.50  --prop_impl_unit                        []
% 7.64/1.50  --share_sel_clauses                     true
% 7.64/1.50  --reset_solvers                         false
% 7.64/1.50  --bc_imp_inh                            [conj_cone]
% 7.64/1.50  --conj_cone_tolerance                   3.
% 7.64/1.50  --extra_neg_conj                        none
% 7.64/1.50  --large_theory_mode                     true
% 7.64/1.50  --prolific_symb_bound                   200
% 7.64/1.50  --lt_threshold                          2000
% 7.64/1.50  --clause_weak_htbl                      true
% 7.64/1.50  --gc_record_bc_elim                     false
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing Options
% 7.64/1.50  
% 7.64/1.50  --preprocessing_flag                    true
% 7.64/1.50  --time_out_prep_mult                    0.1
% 7.64/1.50  --splitting_mode                        input
% 7.64/1.50  --splitting_grd                         true
% 7.64/1.50  --splitting_cvd                         false
% 7.64/1.50  --splitting_cvd_svl                     false
% 7.64/1.50  --splitting_nvd                         32
% 7.64/1.50  --sub_typing                            true
% 7.64/1.50  --prep_gs_sim                           true
% 7.64/1.50  --prep_unflatten                        true
% 7.64/1.50  --prep_res_sim                          true
% 7.64/1.50  --prep_upred                            true
% 7.64/1.50  --prep_sem_filter                       exhaustive
% 7.64/1.50  --prep_sem_filter_out                   false
% 7.64/1.50  --pred_elim                             true
% 7.64/1.50  --res_sim_input                         true
% 7.64/1.50  --eq_ax_congr_red                       true
% 7.64/1.50  --pure_diseq_elim                       true
% 7.64/1.50  --brand_transform                       false
% 7.64/1.50  --non_eq_to_eq                          false
% 7.64/1.50  --prep_def_merge                        true
% 7.64/1.50  --prep_def_merge_prop_impl              false
% 7.64/1.50  --prep_def_merge_mbd                    true
% 7.64/1.50  --prep_def_merge_tr_red                 false
% 7.64/1.50  --prep_def_merge_tr_cl                  false
% 7.64/1.50  --smt_preprocessing                     true
% 7.64/1.50  --smt_ac_axioms                         fast
% 7.64/1.50  --preprocessed_out                      false
% 7.64/1.50  --preprocessed_stats                    false
% 7.64/1.50  
% 7.64/1.50  ------ Abstraction refinement Options
% 7.64/1.50  
% 7.64/1.50  --abstr_ref                             []
% 7.64/1.50  --abstr_ref_prep                        false
% 7.64/1.50  --abstr_ref_until_sat                   false
% 7.64/1.50  --abstr_ref_sig_restrict                funpre
% 7.64/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.50  --abstr_ref_under                       []
% 7.64/1.50  
% 7.64/1.50  ------ SAT Options
% 7.64/1.50  
% 7.64/1.50  --sat_mode                              false
% 7.64/1.50  --sat_fm_restart_options                ""
% 7.64/1.50  --sat_gr_def                            false
% 7.64/1.50  --sat_epr_types                         true
% 7.64/1.50  --sat_non_cyclic_types                  false
% 7.64/1.50  --sat_finite_models                     false
% 7.64/1.50  --sat_fm_lemmas                         false
% 7.64/1.50  --sat_fm_prep                           false
% 7.64/1.50  --sat_fm_uc_incr                        true
% 7.64/1.50  --sat_out_model                         small
% 7.64/1.50  --sat_out_clauses                       false
% 7.64/1.50  
% 7.64/1.50  ------ QBF Options
% 7.64/1.50  
% 7.64/1.50  --qbf_mode                              false
% 7.64/1.50  --qbf_elim_univ                         false
% 7.64/1.50  --qbf_dom_inst                          none
% 7.64/1.50  --qbf_dom_pre_inst                      false
% 7.64/1.50  --qbf_sk_in                             false
% 7.64/1.50  --qbf_pred_elim                         true
% 7.64/1.50  --qbf_split                             512
% 7.64/1.50  
% 7.64/1.50  ------ BMC1 Options
% 7.64/1.50  
% 7.64/1.50  --bmc1_incremental                      false
% 7.64/1.50  --bmc1_axioms                           reachable_all
% 7.64/1.50  --bmc1_min_bound                        0
% 7.64/1.50  --bmc1_max_bound                        -1
% 7.64/1.50  --bmc1_max_bound_default                -1
% 7.64/1.50  --bmc1_symbol_reachability              true
% 7.64/1.50  --bmc1_property_lemmas                  false
% 7.64/1.50  --bmc1_k_induction                      false
% 7.64/1.50  --bmc1_non_equiv_states                 false
% 7.64/1.50  --bmc1_deadlock                         false
% 7.64/1.50  --bmc1_ucm                              false
% 7.64/1.50  --bmc1_add_unsat_core                   none
% 7.64/1.50  --bmc1_unsat_core_children              false
% 7.64/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.50  --bmc1_out_stat                         full
% 7.64/1.50  --bmc1_ground_init                      false
% 7.64/1.50  --bmc1_pre_inst_next_state              false
% 7.64/1.50  --bmc1_pre_inst_state                   false
% 7.64/1.50  --bmc1_pre_inst_reach_state             false
% 7.64/1.50  --bmc1_out_unsat_core                   false
% 7.64/1.50  --bmc1_aig_witness_out                  false
% 7.64/1.50  --bmc1_verbose                          false
% 7.64/1.50  --bmc1_dump_clauses_tptp                false
% 7.64/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.50  --bmc1_dump_file                        -
% 7.64/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.50  --bmc1_ucm_extend_mode                  1
% 7.64/1.50  --bmc1_ucm_init_mode                    2
% 7.64/1.50  --bmc1_ucm_cone_mode                    none
% 7.64/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.50  --bmc1_ucm_relax_model                  4
% 7.64/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.50  --bmc1_ucm_layered_model                none
% 7.64/1.50  --bmc1_ucm_max_lemma_size               10
% 7.64/1.50  
% 7.64/1.50  ------ AIG Options
% 7.64/1.50  
% 7.64/1.50  --aig_mode                              false
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation Options
% 7.64/1.50  
% 7.64/1.50  --instantiation_flag                    true
% 7.64/1.50  --inst_sos_flag                         false
% 7.64/1.50  --inst_sos_phase                        true
% 7.64/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel_side                     none
% 7.64/1.50  --inst_solver_per_active                1400
% 7.64/1.50  --inst_solver_calls_frac                1.
% 7.64/1.50  --inst_passive_queue_type               priority_queues
% 7.64/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.50  --inst_passive_queues_freq              [25;2]
% 7.64/1.50  --inst_dismatching                      true
% 7.64/1.50  --inst_eager_unprocessed_to_passive     true
% 7.64/1.50  --inst_prop_sim_given                   true
% 7.64/1.50  --inst_prop_sim_new                     false
% 7.64/1.50  --inst_subs_new                         false
% 7.64/1.50  --inst_eq_res_simp                      false
% 7.64/1.50  --inst_subs_given                       false
% 7.64/1.50  --inst_orphan_elimination               true
% 7.64/1.50  --inst_learning_loop_flag               true
% 7.64/1.50  --inst_learning_start                   3000
% 7.64/1.50  --inst_learning_factor                  2
% 7.64/1.50  --inst_start_prop_sim_after_learn       3
% 7.64/1.50  --inst_sel_renew                        solver
% 7.64/1.50  --inst_lit_activity_flag                true
% 7.64/1.50  --inst_restr_to_given                   false
% 7.64/1.50  --inst_activity_threshold               500
% 7.64/1.50  --inst_out_proof                        true
% 7.64/1.50  
% 7.64/1.50  ------ Resolution Options
% 7.64/1.50  
% 7.64/1.50  --resolution_flag                       false
% 7.64/1.50  --res_lit_sel                           adaptive
% 7.64/1.50  --res_lit_sel_side                      none
% 7.64/1.50  --res_ordering                          kbo
% 7.64/1.50  --res_to_prop_solver                    active
% 7.64/1.50  --res_prop_simpl_new                    false
% 7.64/1.50  --res_prop_simpl_given                  true
% 7.64/1.50  --res_passive_queue_type                priority_queues
% 7.64/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.50  --res_passive_queues_freq               [15;5]
% 7.64/1.50  --res_forward_subs                      full
% 7.64/1.50  --res_backward_subs                     full
% 7.64/1.50  --res_forward_subs_resolution           true
% 7.64/1.50  --res_backward_subs_resolution          true
% 7.64/1.50  --res_orphan_elimination                true
% 7.64/1.50  --res_time_limit                        2.
% 7.64/1.50  --res_out_proof                         true
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Options
% 7.64/1.50  
% 7.64/1.50  --superposition_flag                    true
% 7.64/1.50  --sup_passive_queue_type                priority_queues
% 7.64/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.50  --demod_completeness_check              fast
% 7.64/1.50  --demod_use_ground                      true
% 7.64/1.50  --sup_to_prop_solver                    passive
% 7.64/1.50  --sup_prop_simpl_new                    true
% 7.64/1.50  --sup_prop_simpl_given                  true
% 7.64/1.50  --sup_fun_splitting                     false
% 7.64/1.50  --sup_smt_interval                      50000
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Simplification Setup
% 7.64/1.50  
% 7.64/1.50  --sup_indices_passive                   []
% 7.64/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_full_bw                           [BwDemod]
% 7.64/1.50  --sup_immed_triv                        [TrivRules]
% 7.64/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_immed_bw_main                     []
% 7.64/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.64/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.64/1.50  
% 7.64/1.50  ------ Combination Options
% 7.64/1.50  
% 7.64/1.50  --comb_res_mult                         3
% 7.64/1.50  --comb_sup_mult                         2
% 7.64/1.50  --comb_inst_mult                        10
% 7.64/1.50  
% 7.64/1.50  ------ Debug Options
% 7.64/1.50  
% 7.64/1.50  --dbg_backtrace                         false
% 7.64/1.50  --dbg_dump_prop_clauses                 false
% 7.64/1.50  --dbg_dump_prop_clauses_file            -
% 7.64/1.50  --dbg_out_stat                          false
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ Proving...
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS status Theorem for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50   Resolution empty clause
% 7.64/1.50  
% 7.64/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  fof(f8,conjecture,(
% 7.64/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f9,negated_conjecture,(
% 7.64/1.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 7.64/1.50    inference(negated_conjecture,[],[f8])).
% 7.64/1.50  
% 7.64/1.50  fof(f19,plain,(
% 7.64/1.50    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 7.64/1.50    inference(ennf_transformation,[],[f9])).
% 7.64/1.50  
% 7.64/1.50  fof(f20,plain,(
% 7.64/1.50    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.64/1.50    inference(flattening,[],[f19])).
% 7.64/1.50  
% 7.64/1.50  fof(f47,plain,(
% 7.64/1.50    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.64/1.50    inference(nnf_transformation,[],[f20])).
% 7.64/1.50  
% 7.64/1.50  fof(f48,plain,(
% 7.64/1.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 7.64/1.50    inference(flattening,[],[f47])).
% 7.64/1.50  
% 7.64/1.50  fof(f49,plain,(
% 7.64/1.50    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)) & (r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)) & r2_hidden(sK9,k3_relat_1(sK10)) & r2_hidden(sK8,k3_relat_1(sK10)) & v2_wellord1(sK10) & v1_relat_1(sK10))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f50,plain,(
% 7.64/1.50    (~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)) & (r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)) & r2_hidden(sK9,k3_relat_1(sK10)) & r2_hidden(sK8,k3_relat_1(sK10)) & v2_wellord1(sK10) & v1_relat_1(sK10)),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f48,f49])).
% 7.64/1.50  
% 7.64/1.50  fof(f88,plain,(
% 7.64/1.50    r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f5,axiom,(
% 7.64/1.50    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f15,plain,(
% 7.64/1.50    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f5])).
% 7.64/1.50  
% 7.64/1.50  fof(f36,plain,(
% 7.64/1.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f15])).
% 7.64/1.50  
% 7.64/1.50  fof(f37,plain,(
% 7.64/1.50    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(rectify,[],[f36])).
% 7.64/1.50  
% 7.64/1.50  fof(f38,plain,(
% 7.64/1.50    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0))))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f39,plain,(
% 7.64/1.50    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & ~r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) & sK3(X0) != sK4(X0) & r2_hidden(sK4(X0),k3_relat_1(X0)) & r2_hidden(sK3(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).
% 7.64/1.50  
% 7.64/1.50  fof(f69,plain,(
% 7.64/1.50    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f39])).
% 7.64/1.50  
% 7.64/1.50  fof(f84,plain,(
% 7.64/1.50    v1_relat_1(sK10)),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f85,plain,(
% 7.64/1.50    v2_wellord1(sK10)),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f3,axiom,(
% 7.64/1.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f13,plain,(
% 7.64/1.50    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f3])).
% 7.64/1.50  
% 7.64/1.50  fof(f30,plain,(
% 7.64/1.50    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f13])).
% 7.64/1.50  
% 7.64/1.50  fof(f31,plain,(
% 7.64/1.50    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(flattening,[],[f30])).
% 7.64/1.50  
% 7.64/1.50  fof(f63,plain,(
% 7.64/1.50    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f31])).
% 7.64/1.50  
% 7.64/1.50  fof(f2,axiom,(
% 7.64/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f12,plain,(
% 7.64/1.50    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f2])).
% 7.64/1.50  
% 7.64/1.50  fof(f25,plain,(
% 7.64/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f12])).
% 7.64/1.50  
% 7.64/1.50  fof(f26,plain,(
% 7.64/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(flattening,[],[f25])).
% 7.64/1.50  
% 7.64/1.50  fof(f27,plain,(
% 7.64/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(rectify,[],[f26])).
% 7.64/1.50  
% 7.64/1.50  fof(f28,plain,(
% 7.64/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f29,plain,(
% 7.64/1.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.64/1.50  
% 7.64/1.50  fof(f56,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f90,plain,(
% 7.64/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(equality_resolution,[],[f56])).
% 7.64/1.50  
% 7.64/1.50  fof(f1,axiom,(
% 7.64/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f11,plain,(
% 7.64/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f1])).
% 7.64/1.50  
% 7.64/1.50  fof(f21,plain,(
% 7.64/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.64/1.50    inference(nnf_transformation,[],[f11])).
% 7.64/1.50  
% 7.64/1.50  fof(f22,plain,(
% 7.64/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.64/1.50    inference(rectify,[],[f21])).
% 7.64/1.50  
% 7.64/1.50  fof(f23,plain,(
% 7.64/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f24,plain,(
% 7.64/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 7.64/1.50  
% 7.64/1.50  fof(f51,plain,(
% 7.64/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f24])).
% 7.64/1.50  
% 7.64/1.50  fof(f86,plain,(
% 7.64/1.50    r2_hidden(sK8,k3_relat_1(sK10))),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f54,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f92,plain,(
% 7.64/1.50    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(equality_resolution,[],[f54])).
% 7.64/1.50  
% 7.64/1.50  fof(f93,plain,(
% 7.64/1.50    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(equality_resolution,[],[f92])).
% 7.64/1.50  
% 7.64/1.50  fof(f87,plain,(
% 7.64/1.50    r2_hidden(sK9,k3_relat_1(sK10))),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f52,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f24])).
% 7.64/1.50  
% 7.64/1.50  fof(f89,plain,(
% 7.64/1.50    ~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 7.64/1.50    inference(cnf_transformation,[],[f50])).
% 7.64/1.50  
% 7.64/1.50  fof(f53,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f24])).
% 7.64/1.50  
% 7.64/1.50  fof(f55,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f91,plain,(
% 7.64/1.50    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(equality_resolution,[],[f55])).
% 7.64/1.50  
% 7.64/1.50  fof(f6,axiom,(
% 7.64/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f16,plain,(
% 7.64/1.50    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(ennf_transformation,[],[f6])).
% 7.64/1.50  
% 7.64/1.50  fof(f75,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f16])).
% 7.64/1.50  
% 7.64/1.50  fof(f7,axiom,(
% 7.64/1.50    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f10,plain,(
% 7.64/1.50    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 7.64/1.50    inference(rectify,[],[f7])).
% 7.64/1.50  
% 7.64/1.50  fof(f17,plain,(
% 7.64/1.50    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(ennf_transformation,[],[f10])).
% 7.64/1.50  
% 7.64/1.50  fof(f18,plain,(
% 7.64/1.50    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(flattening,[],[f17])).
% 7.64/1.50  
% 7.64/1.50  fof(f40,plain,(
% 7.64/1.50    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(nnf_transformation,[],[f18])).
% 7.64/1.50  
% 7.64/1.50  fof(f41,plain,(
% 7.64/1.50    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(flattening,[],[f40])).
% 7.64/1.50  
% 7.64/1.50  fof(f42,plain,(
% 7.64/1.50    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(rectify,[],[f41])).
% 7.64/1.50  
% 7.64/1.50  fof(f45,plain,(
% 7.64/1.50    ( ! [X3] : (! [X1,X0] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) => (~r2_hidden(sK7(X0,X1),X0) & r2_hidden(k4_tarski(sK7(X0,X1),X3),X1)))) )),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f44,plain,(
% 7.64/1.50    ! [X1,X0] : (? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0)) => (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,sK6(X0,X1)),X1)) & r2_hidden(sK6(X0,X1),X0)))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f43,plain,(
% 7.64/1.50    ! [X1,X0] : (? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) => (k1_wellord1(X1,sK5(X0,X1)) = X0 & r2_hidden(sK5(X0,X1),k3_relat_1(X1))))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f46,plain,(
% 7.64/1.50    ! [X0,X1] : ((((k1_wellord1(X1,sK5(X0,X1)) = X0 & r2_hidden(sK5(X0,X1),k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ((~r2_hidden(sK7(X0,X1),X0) & r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X1)) & r2_hidden(sK6(X0,X1),X0))) & (! [X5] : (! [X6] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1)) | ~r2_hidden(X5,X0)) | (! [X7] : (k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).
% 7.64/1.50  
% 7.64/1.50  fof(f77,plain,(
% 7.64/1.50    ( ! [X6,X0,X7,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,X0) | k1_wellord1(X1,X7) != X0 | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f46])).
% 7.64/1.50  
% 7.64/1.50  fof(f94,plain,(
% 7.64/1.50    ( ! [X6,X7,X5,X1] : (r2_hidden(X6,k1_wellord1(X1,X7)) | ~r2_hidden(k4_tarski(X6,X5),X1) | ~r2_hidden(X5,k1_wellord1(X1,X7)) | ~r2_hidden(X7,k3_relat_1(X1)) | ~r1_tarski(k1_wellord1(X1,X7),k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 7.64/1.50    inference(equality_resolution,[],[f77])).
% 7.64/1.50  
% 7.64/1.50  fof(f4,axiom,(
% 7.64/1.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f14,plain,(
% 7.64/1.50    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(ennf_transformation,[],[f4])).
% 7.64/1.50  
% 7.64/1.50  fof(f32,plain,(
% 7.64/1.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(nnf_transformation,[],[f14])).
% 7.64/1.50  
% 7.64/1.50  fof(f33,plain,(
% 7.64/1.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(rectify,[],[f32])).
% 7.64/1.50  
% 7.64/1.50  fof(f34,plain,(
% 7.64/1.50    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0))))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f35,plain,(
% 7.64/1.50    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0) & r2_hidden(sK2(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 7.64/1.50  
% 7.64/1.50  fof(f66,plain,(
% 7.64/1.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f35])).
% 7.64/1.50  
% 7.64/1.50  fof(f60,plain,(
% 7.64/1.50    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f31])).
% 7.64/1.50  
% 7.64/1.50  cnf(c_34,negated_conjecture,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3541,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_23,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.64/1.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | ~ v6_relat_2(X1)
% 7.64/1.50      | ~ v1_relat_1(X1)
% 7.64/1.50      | X0 = X2 ),
% 7.64/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_38,negated_conjecture,
% 7.64/1.50      ( v1_relat_1(sK10) ),
% 7.64/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_952,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.64/1.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.64/1.50      | ~ v6_relat_2(X1)
% 7.64/1.50      | X2 = X0
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_953,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10)
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X1),sK10)
% 7.64/1.50      | ~ v6_relat_2(sK10)
% 7.64/1.50      | X1 = X0 ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_952]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_37,negated_conjecture,
% 7.64/1.50      ( v2_wellord1(sK10) ),
% 7.64/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_11,plain,
% 7.64/1.50      ( v6_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_105,plain,
% 7.64/1.50      ( v6_relat_2(sK10) | ~ v2_wellord1(sK10) | ~ v1_relat_1(sK10) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_955,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(X0,X1),sK10)
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10)
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(X0,k3_relat_1(sK10))
% 7.64/1.50      | X1 = X0 ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_953,c_38,c_37,c_105]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_956,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10)
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X1),sK10)
% 7.64/1.50      | X1 = X0 ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_955]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3527,plain,
% 7.64/1.50      ( X0 = X1
% 7.64/1.50      | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X1),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6,plain,
% 7.64/1.50      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | ~ v1_relat_1(X1)
% 7.64/1.50      | X0 = X2 ),
% 7.64/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1008,plain,
% 7.64/1.50      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | X2 = X0
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1009,plain,
% 7.64/1.50      ( r2_hidden(X0,k1_wellord1(sK10,X1))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X0,X1),sK10)
% 7.64/1.50      | X1 = X0 ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_1008]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3524,plain,
% 7.64/1.50      ( X0 = X1
% 7.64/1.50      | r2_hidden(X1,k1_wellord1(sK10,X0)) = iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5611,plain,
% 7.64/1.50      ( X0 = X1
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
% 7.64/1.50      | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(X1,X0),sK10) = iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_3527,c_3524]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_9796,plain,
% 7.64/1.50      ( X0 = X1
% 7.64/1.50      | r2_hidden(X1,k1_wellord1(sK10,X0)) = iProver_top
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
% 7.64/1.50      | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_5611,c_3524]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.64/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3543,plain,
% 7.64/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.64/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.64/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_10805,plain,
% 7.64/1.50      ( X0 = X1
% 7.64/1.50      | r2_hidden(X1,X2) = iProver_top
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,X1)) = iProver_top
% 7.64/1.50      | r2_hidden(X1,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r1_tarski(k1_wellord1(sK10,X0),X2) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_9796,c_3543]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24574,plain,
% 7.64/1.50      ( sK8 = X0
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top
% 7.64/1.50      | r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_3541,c_10805]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_36,negated_conjecture,
% 7.64/1.50      ( r2_hidden(sK8,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_41,plain,
% 7.64/1.50      ( r2_hidden(sK8,k3_relat_1(sK10)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24879,plain,
% 7.64/1.50      ( r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
% 7.64/1.50      | sK8 = X0 ),
% 7.64/1.50      inference(global_propositional_subsumption,[status(thm)],[c_24574,c_41]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24880,plain,
% 7.64/1.50      ( sK8 = X0
% 7.64/1.50      | r2_hidden(X0,k1_wellord1(sK10,sK9)) = iProver_top
% 7.64/1.50      | r2_hidden(X0,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,X0)) = iProver_top ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_24879]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_8,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_989,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_990,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,X0)) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_989]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3526,plain,
% 7.64/1.50      ( r2_hidden(X0,k1_wellord1(sK10,X0)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24903,plain,
% 7.64/1.50      ( sK9 = sK8
% 7.64/1.50      | r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_24880,c_3526]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_35,negated_conjecture,
% 7.64/1.50      ( r2_hidden(sK9,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_42,plain,
% 7.64/1.50      ( r2_hidden(sK9,k3_relat_1(sK10)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1,plain,
% 7.64/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_33,negated_conjecture,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_298,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(prop_impl,[status(thm)],[c_33]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1085,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | r2_hidden(sK0(X0,X1),X0)
% 7.64/1.50      | k1_wellord1(sK10,sK9) != X1
% 7.64/1.50      | k1_wellord1(sK10,sK8) != X0 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_1,c_298]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1086,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_1085]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1087,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_0,plain,
% 7.64/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1095,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | ~ r2_hidden(sK0(X0,X1),X1)
% 7.64/1.50      | k1_wellord1(sK10,sK9) != X1
% 7.64/1.50      | k1_wellord1(sK10,sK8) != X0 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_298]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1096,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | ~ r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_1095]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1097,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3902,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,X0),sK10)
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,X0))
% 7.64/1.50      | X0 = sK8 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_1009]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4563,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,sK9))
% 7.64/1.50      | sK9 = sK8 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_3902]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4564,plain,
% 7.64/1.50      ( sK9 = sK8
% 7.64/1.50      | r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_4563]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | ~ v1_relat_1(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_998,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X2),X1)
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_999,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X1),sK10) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_998]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6432,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10)
% 7.64/1.50      | ~ r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_999]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6433,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK8)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_6432]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4064,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,X0),sK10)
% 7.64/1.50      | ~ r2_hidden(sK8,k1_wellord1(sK10,X0)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_999]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7544,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10)
% 7.64/1.50      | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_4064]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7545,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,sK9)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_7544]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24,plain,
% 7.64/1.50      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_881,plain,
% 7.64/1.50      ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0)) | sK10 != X0 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_882,plain,
% 7.64/1.50      ( r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10)) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_881]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_31,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | r2_hidden(X3,k1_wellord1(X1,X2))
% 7.64/1.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 7.64/1.50      | ~ v2_wellord1(X1)
% 7.64/1.50      | ~ v1_relat_1(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_609,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 7.64/1.50      | r2_hidden(X3,k1_wellord1(X1,X2))
% 7.64/1.50      | ~ r2_hidden(X2,k3_relat_1(X1))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X3,X0),X1)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
% 7.64/1.50      | ~ v1_relat_1(X1)
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_610,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
% 7.64/1.50      | r2_hidden(X2,k1_wellord1(sK10,X1))
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X2,X0),sK10)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10))
% 7.64/1.50      | ~ v1_relat_1(sK10) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_609]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_612,plain,
% 7.64/1.50      ( ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X2,X0),sK10)
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | r2_hidden(X2,k1_wellord1(sK10,X1))
% 7.64/1.50      | ~ r2_hidden(X0,k1_wellord1(sK10,X1)) ),
% 7.64/1.50      inference(global_propositional_subsumption,[status(thm)],[c_610,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_613,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
% 7.64/1.50      | r2_hidden(X2,k1_wellord1(sK10,X1))
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X2,X0),sK10)
% 7.64/1.50      | ~ r1_tarski(k1_wellord1(sK10,X1),k3_relat_1(sK10)) ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_612]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1027,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
% 7.64/1.50      | r2_hidden(X2,k1_wellord1(sK10,X1))
% 7.64/1.50      | ~ r2_hidden(X1,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X2,X0),sK10) ),
% 7.64/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_882,c_613]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3760,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k1_wellord1(sK10,sK9))
% 7.64/1.50      | r2_hidden(X1,k1_wellord1(sK10,sK9))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X1,X0),sK10)
% 7.64/1.50      | ~ r2_hidden(sK9,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_1027]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4253,plain,
% 7.64/1.50      ( r2_hidden(X0,k1_wellord1(sK10,sK9))
% 7.64/1.50      | ~ r2_hidden(k4_tarski(X0,sK8),sK10)
% 7.64/1.50      | ~ r2_hidden(sK9,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_3760]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24542,plain,
% 7.64/1.50      ( ~ r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10)
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9))
% 7.64/1.50      | ~ r2_hidden(sK9,k3_relat_1(sK10))
% 7.64/1.50      | ~ r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_4253]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24543,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),sK8),sK10) != iProver_top
% 7.64/1.50      | r2_hidden(sK0(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)),k1_wellord1(sK10,sK9)) = iProver_top
% 7.64/1.50      | r2_hidden(sK9,k3_relat_1(sK10)) != iProver_top
% 7.64/1.50      | r2_hidden(sK8,k1_wellord1(sK10,sK9)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_24542]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_25149,plain,
% 7.64/1.50      ( sK9 = sK8 | r2_hidden(sK8,k1_wellord1(sK10,sK9)) = iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_24903,c_42,c_1087,c_1097,c_4564,c_6433,c_7545,c_24543]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_25153,plain,
% 7.64/1.50      ( sK9 = sK8 ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_25149,c_42,c_1087,c_1097,c_4564,c_6433,c_7545,c_24543,
% 7.64/1.50                 c_24903]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3542,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK9),sK10) != iProver_top
% 7.64/1.50      | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_25181,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK8),sK10) != iProver_top
% 7.64/1.50      | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8)) != iProver_top ),
% 7.64/1.50      inference(demodulation,[status(thm)],[c_25153,c_3542]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_17,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 7.64/1.50      | ~ v1_relat_2(X1)
% 7.64/1.50      | ~ v1_relat_1(X1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_975,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 7.64/1.50      | ~ v1_relat_2(X1)
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_976,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X0),sK10)
% 7.64/1.50      | ~ v1_relat_2(sK10) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_975]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14,plain,
% 7.64/1.50      ( v1_relat_2(X0) | ~ v2_wellord1(X0) | ~ v1_relat_1(X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_567,plain,
% 7.64/1.50      ( v1_relat_2(X0) | ~ v1_relat_1(X0) | sK10 != X0 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_37]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_568,plain,
% 7.64/1.50      ( v1_relat_2(sK10) | ~ v1_relat_1(sK10) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_567]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_96,plain,
% 7.64/1.50      ( v1_relat_2(sK10) | ~ v2_wellord1(sK10) | ~ v1_relat_1(sK10) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_570,plain,
% 7.64/1.50      ( v1_relat_2(sK10) ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_568,c_38,c_37,c_96]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_853,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(X1))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X0),X1)
% 7.64/1.50      | ~ v1_relat_1(X1)
% 7.64/1.50      | sK10 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_570]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_854,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10))
% 7.64/1.50      | r2_hidden(k4_tarski(X0,X0),sK10)
% 7.64/1.50      | ~ v1_relat_1(sK10) ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_853]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_858,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(X0,X0),sK10) | ~ r2_hidden(X0,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(global_propositional_subsumption,[status(thm)],[c_854,c_38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_859,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10)) | r2_hidden(k4_tarski(X0,X0),sK10) ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_858]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_978,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(X0,X0),sK10) | ~ r2_hidden(X0,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_976,c_38,c_854]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_979,plain,
% 7.64/1.50      ( ~ r2_hidden(X0,k3_relat_1(sK10)) | r2_hidden(k4_tarski(X0,X0),sK10) ),
% 7.64/1.50      inference(renaming,[status(thm)],[c_978]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3735,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK8),sK10)
% 7.64/1.50      | ~ r2_hidden(sK8,k3_relat_1(sK10)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_979]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3736,plain,
% 7.64/1.50      ( r2_hidden(k4_tarski(sK8,sK8),sK10) = iProver_top
% 7.64/1.50      | r2_hidden(sK8,k3_relat_1(sK10)) != iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_3735]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_25307,plain,
% 7.64/1.50      ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8)) != iProver_top ),
% 7.64/1.50      inference(global_propositional_subsumption,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_25181,c_41,c_3736]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3544,plain,
% 7.64/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.64/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3545,plain,
% 7.64/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.64/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.64/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4096,plain,
% 7.64/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.64/1.50      inference(superposition,[status(thm)],[c_3544,c_3545]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_25312,plain,
% 7.64/1.50      ( $false ),
% 7.64/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_25307,c_4096]) ).
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  ------                               Statistics
% 7.64/1.50  
% 7.64/1.50  ------ General
% 7.64/1.50  
% 7.64/1.50  abstr_ref_over_cycles:                  0
% 7.64/1.50  abstr_ref_under_cycles:                 0
% 7.64/1.50  gc_basic_clause_elim:                   0
% 7.64/1.50  forced_gc_time:                         0
% 7.64/1.50  parsing_time:                           0.01
% 7.64/1.50  unif_index_cands_time:                  0.
% 7.64/1.50  unif_index_add_time:                    0.
% 7.64/1.50  orderings_time:                         0.
% 7.64/1.50  out_proof_time:                         0.012
% 7.64/1.50  total_time:                             0.588
% 7.64/1.50  num_of_symbols:                         54
% 7.64/1.50  num_of_terms:                           14653
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing
% 7.64/1.50  
% 7.64/1.50  num_of_splits:                          0
% 7.64/1.50  num_of_split_atoms:                     0
% 7.64/1.50  num_of_reused_defs:                     0
% 7.64/1.50  num_eq_ax_congr_red:                    33
% 7.64/1.50  num_of_sem_filtered_clauses:            1
% 7.64/1.50  num_of_subtypes:                        0
% 7.64/1.50  monotx_restored_types:                  0
% 7.64/1.50  sat_num_of_epr_types:                   0
% 7.64/1.50  sat_num_of_non_cyclic_types:            0
% 7.64/1.50  sat_guarded_non_collapsed_types:        0
% 7.64/1.50  num_pure_diseq_elim:                    0
% 7.64/1.50  simp_replaced_by:                       0
% 7.64/1.50  res_preprocessed:                       134
% 7.64/1.50  prep_upred:                             0
% 7.64/1.50  prep_unflattend:                        180
% 7.64/1.50  smt_new_axioms:                         0
% 7.64/1.50  pred_elim_cands:                        2
% 7.64/1.50  pred_elim:                              7
% 7.64/1.50  pred_elim_cl:                           15
% 7.64/1.50  pred_elim_cycles:                       12
% 7.64/1.50  merged_defs:                            8
% 7.64/1.50  merged_defs_ncl:                        0
% 7.64/1.50  bin_hyper_res:                          8
% 7.64/1.50  prep_cycles:                            4
% 7.64/1.50  pred_elim_time:                         0.041
% 7.64/1.50  splitting_time:                         0.
% 7.64/1.50  sem_filter_time:                        0.
% 7.64/1.50  monotx_time:                            0.
% 7.64/1.50  subtype_inf_time:                       0.
% 7.64/1.50  
% 7.64/1.50  ------ Problem properties
% 7.64/1.50  
% 7.64/1.50  clauses:                                24
% 7.64/1.50  conjectures:                            4
% 7.64/1.50  epr:                                    1
% 7.64/1.50  horn:                                   11
% 7.64/1.50  ground:                                 4
% 7.64/1.50  unary:                                  4
% 7.64/1.50  binary:                                 6
% 7.64/1.50  lits:                                   68
% 7.64/1.50  lits_eq:                                16
% 7.64/1.50  fd_pure:                                0
% 7.64/1.50  fd_pseudo:                              0
% 7.64/1.50  fd_cond:                                3
% 7.64/1.50  fd_pseudo_cond:                         4
% 7.64/1.50  ac_symbols:                             0
% 7.64/1.50  
% 7.64/1.50  ------ Propositional Solver
% 7.64/1.50  
% 7.64/1.50  prop_solver_calls:                      30
% 7.64/1.50  prop_fast_solver_calls:                 2055
% 7.64/1.50  smt_solver_calls:                       0
% 7.64/1.50  smt_fast_solver_calls:                  0
% 7.64/1.50  prop_num_of_clauses:                    6362
% 7.64/1.50  prop_preprocess_simplified:             13799
% 7.64/1.50  prop_fo_subsumed:                       30
% 7.64/1.50  prop_solver_time:                       0.
% 7.64/1.50  smt_solver_time:                        0.
% 7.64/1.50  smt_fast_solver_time:                   0.
% 7.64/1.50  prop_fast_solver_time:                  0.
% 7.64/1.50  prop_unsat_core_time:                   0.
% 7.64/1.50  
% 7.64/1.50  ------ QBF
% 7.64/1.50  
% 7.64/1.50  qbf_q_res:                              0
% 7.64/1.50  qbf_num_tautologies:                    0
% 7.64/1.50  qbf_prep_cycles:                        0
% 7.64/1.50  
% 7.64/1.50  ------ BMC1
% 7.64/1.50  
% 7.64/1.50  bmc1_current_bound:                     -1
% 7.64/1.50  bmc1_last_solved_bound:                 -1
% 7.64/1.50  bmc1_unsat_core_size:                   -1
% 7.64/1.50  bmc1_unsat_core_parents_size:           -1
% 7.64/1.50  bmc1_merge_next_fun:                    0
% 7.64/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation
% 7.64/1.50  
% 7.64/1.50  inst_num_of_clauses:                    1516
% 7.64/1.50  inst_num_in_passive:                    730
% 7.64/1.50  inst_num_in_active:                     669
% 7.64/1.50  inst_num_in_unprocessed:                117
% 7.64/1.50  inst_num_of_loops:                      890
% 7.64/1.50  inst_num_of_learning_restarts:          0
% 7.64/1.50  inst_num_moves_active_passive:          218
% 7.64/1.50  inst_lit_activity:                      0
% 7.64/1.50  inst_lit_activity_moves:                0
% 7.64/1.50  inst_num_tautologies:                   0
% 7.64/1.50  inst_num_prop_implied:                  0
% 7.64/1.50  inst_num_existing_simplified:           0
% 7.64/1.50  inst_num_eq_res_simplified:             0
% 7.64/1.50  inst_num_child_elim:                    0
% 7.64/1.50  inst_num_of_dismatching_blockings:      801
% 7.64/1.50  inst_num_of_non_proper_insts:           1615
% 7.64/1.50  inst_num_of_duplicates:                 0
% 7.64/1.50  inst_inst_num_from_inst_to_res:         0
% 7.64/1.50  inst_dismatching_checking_time:         0.
% 7.64/1.50  
% 7.64/1.50  ------ Resolution
% 7.64/1.50  
% 7.64/1.50  res_num_of_clauses:                     0
% 7.64/1.50  res_num_in_passive:                     0
% 7.64/1.50  res_num_in_active:                      0
% 7.64/1.50  res_num_of_loops:                       138
% 7.64/1.50  res_forward_subset_subsumed:            183
% 7.64/1.50  res_backward_subset_subsumed:           2
% 7.64/1.50  res_forward_subsumed:                   0
% 7.64/1.50  res_backward_subsumed:                  18
% 7.64/1.50  res_forward_subsumption_resolution:     0
% 7.64/1.50  res_backward_subsumption_resolution:    1
% 7.64/1.50  res_clause_to_clause_subsumption:       8070
% 7.64/1.50  res_orphan_elimination:                 0
% 7.64/1.50  res_tautology_del:                      160
% 7.64/1.50  res_num_eq_res_simplified:              0
% 7.64/1.50  res_num_sel_changes:                    0
% 7.64/1.50  res_moves_from_active_to_pass:          0
% 7.64/1.50  
% 7.64/1.50  ------ Superposition
% 7.64/1.50  
% 7.64/1.50  sup_time_total:                         0.
% 7.64/1.50  sup_time_generating:                    0.
% 7.64/1.50  sup_time_sim_full:                      0.
% 7.64/1.50  sup_time_sim_immed:                     0.
% 7.64/1.50  
% 7.64/1.50  sup_num_of_clauses:                     613
% 7.64/1.50  sup_num_in_active:                      150
% 7.64/1.50  sup_num_in_passive:                     463
% 7.64/1.50  sup_num_of_loops:                       177
% 7.64/1.50  sup_fw_superposition:                   333
% 7.64/1.50  sup_bw_superposition:                   612
% 7.64/1.50  sup_immediate_simplified:               254
% 7.64/1.50  sup_given_eliminated:                   0
% 7.64/1.50  comparisons_done:                       0
% 7.64/1.50  comparisons_avoided:                    15
% 7.64/1.50  
% 7.64/1.50  ------ Simplifications
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  sim_fw_subset_subsumed:                 80
% 7.64/1.50  sim_bw_subset_subsumed:                 61
% 7.64/1.50  sim_fw_subsumed:                        111
% 7.64/1.50  sim_bw_subsumed:                        4
% 7.64/1.50  sim_fw_subsumption_res:                 1
% 7.64/1.50  sim_bw_subsumption_res:                 0
% 7.64/1.50  sim_tautology_del:                      24
% 7.64/1.50  sim_eq_tautology_del:                   18
% 7.64/1.50  sim_eq_res_simp:                        10
% 7.64/1.50  sim_fw_demodulated:                     0
% 7.64/1.50  sim_bw_demodulated:                     27
% 7.64/1.50  sim_light_normalised:                   0
% 7.64/1.50  sim_joinable_taut:                      0
% 7.64/1.50  sim_joinable_simp:                      0
% 7.64/1.50  sim_ac_normalised:                      0
% 7.64/1.50  sim_smt_subsumption:                    0
% 7.64/1.50  
%------------------------------------------------------------------------------
