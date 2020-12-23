%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:02 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 307 expanded)
%              Number of clauses        :   71 (  93 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  464 (1577 expanded)
%              Number of equality atoms :  107 ( 245 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).

fof(f48,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(X2,sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f35,f38,f37,f36])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK6(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK6(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f44,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

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
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f9,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) )
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & ! [X1] :
          ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & ! [X1] :
            ( v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(k3_tarski(sK7))
      & ! [X1] :
          ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ v3_ordinal1(k3_tarski(sK7))
    & ! [X1] :
        ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f40])).

fof(f67,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK7) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ~ v3_ordinal1(k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1740,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,plain,
    ( r2_hidden(X0,sK6(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1729,plain,
    ( r2_hidden(X0,sK6(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1728,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2907,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(sK6(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1728])).

cnf(c_13971,plain,
    ( v3_ordinal1(sK6(X0,sK1(k3_tarski(X0)))) != iProver_top
    | v3_ordinal1(sK1(k3_tarski(X0))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_2907])).

cnf(c_14225,plain,
    ( v3_ordinal1(sK6(sK7,sK1(k3_tarski(sK7)))) != iProver_top
    | v3_ordinal1(sK1(k3_tarski(sK7))) = iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13971])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1741,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13970,plain,
    ( v3_ordinal1(sK6(X0,sK2(k3_tarski(X0)))) != iProver_top
    | v3_ordinal1(sK2(k3_tarski(X0))) = iProver_top
    | v2_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_2907])).

cnf(c_14222,plain,
    ( v3_ordinal1(sK6(sK7,sK2(k3_tarski(sK7)))) != iProver_top
    | v3_ordinal1(sK2(k3_tarski(sK7))) = iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13970])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2837,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK7)),X0)
    | r1_tarski(sK0(k3_tarski(sK7)),X0)
    | ~ v1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8377,plain,
    ( ~ r2_hidden(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7))))
    | r1_tarski(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7))))
    | ~ v1_ordinal1(sK6(sK7,sK0(k3_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_2837])).

cnf(c_8384,plain,
    ( r2_hidden(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) != iProver_top
    | r1_tarski(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) = iProver_top
    | v1_ordinal1(sK6(sK7,sK0(k3_tarski(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8377])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2594,plain,
    ( ~ r2_hidden(X0,sK6(sK7,sK0(k3_tarski(sK7))))
    | r2_hidden(X0,k3_tarski(sK7))
    | ~ r2_hidden(sK6(sK7,sK0(k3_tarski(sK7))),sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5178,plain,
    ( ~ r2_hidden(sK6(sK7,sK0(k3_tarski(sK7))),sK7)
    | ~ r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7))))
    | r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_5181,plain,
    ( r2_hidden(sK6(sK7,sK0(k3_tarski(sK7))),sK7) != iProver_top
    | r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) != iProver_top
    | r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5178])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2370,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),X0)
    | ~ r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK0(k3_tarski(sK7)))
    | ~ r1_tarski(sK0(k3_tarski(sK7)),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5177,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7))))
    | ~ r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK0(k3_tarski(sK7)))
    | ~ r1_tarski(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_2370])).

cnf(c_5179,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) = iProver_top
    | r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK0(k3_tarski(sK7))) != iProver_top
    | r1_tarski(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5177])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1746,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK6(X1,X0),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1730,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK6(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1725,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2915,plain,
    ( r2_hidden(X0,k3_tarski(sK7)) != iProver_top
    | v3_ordinal1(sK6(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_1725])).

cnf(c_3071,plain,
    ( v1_ordinal1(k3_tarski(sK7)) = iProver_top
    | v3_ordinal1(sK6(sK7,sK0(k3_tarski(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_2915])).

cnf(c_16,plain,
    ( v1_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1748,plain,
    ( v1_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3479,plain,
    ( v1_ordinal1(sK6(sK7,sK0(k3_tarski(sK7)))) = iProver_top
    | v1_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_1748])).

cnf(c_3075,plain,
    ( v3_ordinal1(sK6(sK7,sK1(k3_tarski(sK7)))) = iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_2915])).

cnf(c_3074,plain,
    ( v3_ordinal1(sK6(sK7,sK2(k3_tarski(sK7)))) = iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_2915])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2439,plain,
    ( r2_hidden(sK1(k3_tarski(sK7)),sK2(k3_tarski(sK7)))
    | r2_hidden(sK2(k3_tarski(sK7)),sK1(k3_tarski(sK7)))
    | ~ v3_ordinal1(sK1(k3_tarski(sK7)))
    | ~ v3_ordinal1(sK2(k3_tarski(sK7)))
    | sK1(k3_tarski(sK7)) = sK2(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2440,plain,
    ( sK1(k3_tarski(sK7)) = sK2(k3_tarski(sK7))
    | r2_hidden(sK1(k3_tarski(sK7)),sK2(k3_tarski(sK7))) = iProver_top
    | r2_hidden(sK2(k3_tarski(sK7)),sK1(k3_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK1(k3_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK2(k3_tarski(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2179,plain,
    ( r2_hidden(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7))))
    | ~ r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2183,plain,
    ( r2_hidden(sK0(k3_tarski(sK7)),sK6(sK7,sK0(k3_tarski(sK7)))) = iProver_top
    | r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2179])).

cnf(c_2180,plain,
    ( r2_hidden(sK6(sK7,sK0(k3_tarski(sK7))),sK7)
    | ~ r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2181,plain,
    ( r2_hidden(sK6(sK7,sK0(k3_tarski(sK7))),sK7) = iProver_top
    | r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_12,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2145,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK0(k3_tarski(sK7)))
    | r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2152,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),sK0(k3_tarski(sK7))) = iProver_top
    | r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2145])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2146,plain,
    ( ~ r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),k3_tarski(sK7))
    | r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2150,plain,
    ( r2_hidden(sK3(sK0(k3_tarski(sK7)),k3_tarski(sK7)),k3_tarski(sK7)) != iProver_top
    | r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2146])).

cnf(c_6,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2027,plain,
    ( v2_ordinal1(k3_tarski(sK7))
    | sK1(k3_tarski(sK7)) != sK2(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2041,plain,
    ( sK1(k3_tarski(sK7)) != sK2(k3_tarski(sK7))
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2030,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK7)),sK2(k3_tarski(sK7)))
    | v2_ordinal1(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2035,plain,
    ( r2_hidden(sK1(k3_tarski(sK7)),sK2(k3_tarski(sK7))) != iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2031,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK7)),sK1(k3_tarski(sK7)))
    | v2_ordinal1(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2033,plain,
    ( r2_hidden(sK2(k3_tarski(sK7)),sK1(k3_tarski(sK7))) != iProver_top
    | v2_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_2,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1965,plain,
    ( ~ r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7))
    | v1_ordinal1(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1970,plain,
    ( r1_tarski(sK0(k3_tarski(sK7)),k3_tarski(sK7)) != iProver_top
    | v1_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_1966,plain,
    ( r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7))
    | v1_ordinal1(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1968,plain,
    ( r2_hidden(sK0(k3_tarski(sK7)),k3_tarski(sK7)) = iProver_top
    | v1_ordinal1(k3_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_14,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | ~ v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1936,plain,
    ( ~ v1_ordinal1(k3_tarski(sK7))
    | v3_ordinal1(k3_tarski(sK7))
    | ~ v2_ordinal1(k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1937,plain,
    ( v1_ordinal1(k3_tarski(sK7)) != iProver_top
    | v3_ordinal1(k3_tarski(sK7)) = iProver_top
    | v2_ordinal1(k3_tarski(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_25,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,plain,
    ( v3_ordinal1(k3_tarski(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14225,c_14222,c_8384,c_5181,c_5179,c_3479,c_3075,c_3074,c_2440,c_2183,c_2181,c_2152,c_2150,c_2041,c_2035,c_2033,c_1970,c_1968,c_1937,c_30])).


%------------------------------------------------------------------------------
