%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:02 EST 2020

% Result     : Theorem 51.73s
% Output     : CNFRefutation 51.73s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 884 expanded)
%              Number of clauses        :  162 ( 271 expanded)
%              Number of leaves         :   23 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :  830 (4063 expanded)
%              Number of equality atoms :  240 ( 608 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f71,f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f44,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK5),X0)
        & r2_hidden(sK5,X0)
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK4)
            & r2_hidden(X1,sK4)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK4) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK4)
            | ~ r2_hidden(X2,sK4)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK4) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK5),sK4)
        & r2_hidden(sK5,sK4)
        & v3_ordinal1(sK5) )
      | ~ v4_ordinal1(sK4) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK4)
          | ~ r2_hidden(X2,sK4)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK4) )
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f75,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK4) ) ),
    inference(definition_unfolding,[],[f75,f58])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f63,f58])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f58])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f69,f58])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f72,f58])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f78,plain,
    ( ~ r2_hidden(k1_ordinal1(sK5),sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(definition_unfolding,[],[f78,f58])).

fof(f77,plain,
    ( r2_hidden(sK5,sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,
    ( v3_ordinal1(sK5)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f59,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f66,f58])).

fof(f93,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f80])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_91950,plain,
    ( ~ r1_ordinal1(X0,sK5)
    | r1_tarski(X0,sK5)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_151992,plain,
    ( ~ r1_ordinal1(sK3(sK4,sK5),sK5)
    | r1_tarski(sK3(sK4,sK5),sK5)
    | ~ v3_ordinal1(sK3(sK4,sK5))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_91950])).

cnf(c_22,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_90051,plain,
    ( r1_ordinal1(X0,sK5)
    | ~ r2_hidden(X0,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_109027,plain,
    ( r1_ordinal1(sK3(sK4,sK5),sK5)
    | ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v3_ordinal1(sK3(sK4,sK5))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_90051])).

cnf(c_1419,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_89143,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_108963,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ r2_hidden(sK3(sK4,sK5),X0)
    | k2_xboole_0(sK5,k1_tarski(sK5)) != sK3(sK4,sK5)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_89143])).

cnf(c_108965,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ r2_hidden(sK3(sK4,sK5),sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) != sK3(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_108963])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_90405,plain,
    ( ~ r2_hidden(sK5,X0)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_104524,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_90405])).

cnf(c_102089,plain,
    ( ~ r1_ordinal1(sK5,sK5)
    | r1_tarski(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_91950])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_89746,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK3(X2,X0))
    | ~ r1_tarski(sK3(X2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_90834,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK3(X1,sK5))
    | ~ r1_tarski(sK3(X1,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_89746])).

cnf(c_93878,plain,
    ( ~ r2_hidden(sK5,sK3(X0,sK5))
    | r2_hidden(sK5,sK5)
    | ~ r1_tarski(sK3(X0,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_90834])).

cnf(c_93885,plain,
    ( ~ r2_hidden(sK5,sK3(sK4,sK5))
    | r2_hidden(sK5,sK5)
    | ~ r1_tarski(sK3(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_93878])).

cnf(c_91937,plain,
    ( r1_ordinal1(sK5,sK5)
    | ~ r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_90051])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2028,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2030,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3835,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2030])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2007,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2019,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2029,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X2) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4734,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2029])).

cnf(c_46693,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(k2_xboole_0(sK1(X0,X1),k1_tarski(sK1(X0,X1))),X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_4734])).

cnf(c_47436,plain,
    ( k3_tarski(sK4) = X0
    | r2_hidden(sK2(sK4,X0),sK4) = iProver_top
    | r2_hidden(sK1(sK4,X0),sK4) != iProver_top
    | v3_ordinal1(sK1(sK4,X0)) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_46693])).

cnf(c_47656,plain,
    ( k3_tarski(sK4) = X0
    | r2_hidden(sK2(sK4,X0),sK4) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | v3_ordinal1(sK1(sK4,X0)) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_47436])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_74,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_76,plain,
    ( k3_tarski(sK4) != sK4
    | v4_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2638,plain,
    ( r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4)
    | ~ r2_hidden(sK1(sK4,sK4),sK4)
    | ~ v3_ordinal1(sK1(sK4,sK4))
    | v4_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2639,plain,
    ( r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4) = iProver_top
    | r2_hidden(sK1(sK4,sK4),sK4) != iProver_top
    | v3_ordinal1(sK1(sK4,sK4)) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2638])).

cnf(c_2341,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK1(sK4,sK4),X0)
    | ~ r2_hidden(sK1(sK4,sK4),sK4)
    | k3_tarski(sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3249,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4)
    | ~ r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))))
    | ~ r2_hidden(sK1(sK4,sK4),sK4)
    | k3_tarski(sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_3253,plain,
    ( k3_tarski(sK4) = sK4
    | r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4) != iProver_top
    | r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3249])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2027,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3951,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(sK2(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_2030])).

cnf(c_3958,plain,
    ( k3_tarski(sK4) = sK4
    | r2_hidden(sK1(sK4,sK4),sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3951])).

cnf(c_5318,plain,
    ( r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5319,plain,
    ( r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5318])).

cnf(c_9087,plain,
    ( ~ r1_ordinal1(sK2(sK4,sK4),sK4)
    | r1_tarski(sK2(sK4,sK4),sK4)
    | ~ v3_ordinal1(sK2(sK4,sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_9094,plain,
    ( r1_ordinal1(sK2(sK4,sK4),sK4) != iProver_top
    | r1_tarski(sK2(sK4,sK4),sK4) = iProver_top
    | v3_ordinal1(sK2(sK4,sK4)) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9087])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2016,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3952,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v3_ordinal1(sK2(X0,X1)) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_2016])).

cnf(c_39068,plain,
    ( k3_tarski(X0) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK2(X0,X1)) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3952,c_2016])).

cnf(c_39107,plain,
    ( k3_tarski(sK4) = sK4
    | v3_ordinal1(sK2(sK4,sK4)) != iProver_top
    | v3_ordinal1(sK1(sK4,sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39068])).

cnf(c_47668,plain,
    ( k3_tarski(sK4) = sK4
    | r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
    | v3_ordinal1(sK1(sK4,sK4)) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_47436])).

cnf(c_3836,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2016])).

cnf(c_3851,plain,
    ( k3_tarski(sK4) = sK4
    | r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
    | v3_ordinal1(sK1(sK4,sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3836])).

cnf(c_47676,plain,
    ( r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47668,c_29,c_76,c_3851])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2018,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2012,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3062,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2018,c_2012])).

cnf(c_39,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_54,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_58,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7376,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3062,c_39,c_54,c_58])).

cnf(c_7377,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7376])).

cnf(c_47683,plain,
    ( r1_ordinal1(sK2(sK4,sK4),sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_47676,c_7377])).

cnf(c_47687,plain,
    ( v3_ordinal1(sK2(sK4,sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v4_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_47676,c_2016])).

cnf(c_47744,plain,
    ( v4_ordinal1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47656,c_29,c_76,c_2639,c_3253,c_3958,c_5319,c_9094,c_39107,c_47683,c_47687])).

cnf(c_44856,plain,
    ( ~ r1_ordinal1(sK4,k3_tarski(X0))
    | r1_tarski(sK4,k3_tarski(X0))
    | ~ v3_ordinal1(k3_tarski(X0))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_44868,plain,
    ( ~ r1_ordinal1(sK4,k3_tarski(sK4))
    | r1_tarski(sK4,k3_tarski(sK4))
    | ~ v3_ordinal1(k3_tarski(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_44856])).

cnf(c_1417,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_42319,plain,
    ( k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) = k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38258,plain,
    ( r2_hidden(sK5,sK3(X0,sK5))
    | ~ r2_hidden(sK5,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_38274,plain,
    ( r2_hidden(sK5,sK3(sK4,sK5))
    | ~ r2_hidden(sK5,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_38258])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38259,plain,
    ( r2_hidden(sK3(X0,sK5),X0)
    | ~ r2_hidden(sK5,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_38270,plain,
    ( r2_hidden(sK3(sK4,sK5),sK4)
    | ~ r2_hidden(sK5,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_38259])).

cnf(c_17127,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_38256,plain,
    ( r2_hidden(sK5,k3_tarski(X0))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_tarski(sK4,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_17127])).

cnf(c_38262,plain,
    ( r2_hidden(sK5,k3_tarski(sK4))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_tarski(sK4,k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_38256])).

cnf(c_3048,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2)))
    | X0 != X2
    | X1 != k2_xboole_0(X2,k1_tarski(X2)) ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_15200,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0)))
    | X1 != X0
    | k2_xboole_0(X0,k1_tarski(X0)) != k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_3048])).

cnf(c_28546,plain,
    ( ~ r2_hidden(k3_tarski(sK4),k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
    | r2_hidden(sK4,k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
    | k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) != k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4)))
    | sK4 != k3_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_15200])).

cnf(c_3035,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | X1 != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))
    | X0 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_28006,plain,
    ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | X0 != k2_xboole_0(sK5,k1_tarski(sK5))
    | k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_28008,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r2_hidden(sK4,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))
    | sK4 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_28006])).

cnf(c_18993,plain,
    ( r1_ordinal1(sK4,k3_tarski(sK4))
    | ~ r2_hidden(sK4,k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
    | ~ v3_ordinal1(k3_tarski(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_169,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_17])).

cnf(c_170,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_2365,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | ~ r2_hidden(X0,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_17156,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_2365])).

cnf(c_17163,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17156])).

cnf(c_4880,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_8440,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_4880])).

cnf(c_8442,plain,
    ( r1_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r2_hidden(sK4,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_8440])).

cnf(c_8267,plain,
    ( ~ r2_hidden(sK3(X0,sK5),X1)
    | r2_hidden(sK3(X0,sK5),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_8269,plain,
    ( r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ r2_hidden(sK3(sK4,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_8267])).

cnf(c_2281,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r1_tarski(X1,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4300,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_2281])).

cnf(c_8237,plain,
    ( ~ r2_hidden(sK3(X0,sK5),k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(sK3(X0,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_4300])).

cnf(c_8258,plain,
    ( r2_hidden(sK3(sK4,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_8237])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2132,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r2_hidden(X0,k2_xboole_0(sK5,k1_tarski(sK5)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_8223,plain,
    ( ~ r2_hidden(sK3(X0,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r2_hidden(sK3(X0,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK3(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_8229,plain,
    ( ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_8223])).

cnf(c_7082,plain,
    ( r2_hidden(k3_tarski(sK4),k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2974,plain,
    ( ~ r1_ordinal1(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4958,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_2974])).

cnf(c_4967,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | r1_tarski(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_4958])).

cnf(c_4569,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) = k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_4209,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3141,plain,
    ( ~ r2_hidden(sK3(X0,sK5),X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(sK3(X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3143,plain,
    ( ~ r2_hidden(sK3(sK4,sK5),sK4)
    | v3_ordinal1(sK3(sK4,sK5))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_3141])).

cnf(c_21,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2961,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2967,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0) != iProver_top
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2961])).

cnf(c_2969,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) != iProver_top
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(sK4,k1_tarski(sK4))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2967])).

cnf(c_2917,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
    | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0)))
    | X0 = k2_xboole_0(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2918,plain,
    ( X0 = k2_xboole_0(sK5,k1_tarski(sK5))
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0) = iProver_top
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_2920,plain,
    ( sK4 = k2_xboole_0(sK5,k1_tarski(sK5))
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
    | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_1418,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2792,plain,
    ( k3_tarski(X0) != X1
    | sK4 != X1
    | sK4 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_2793,plain,
    ( k3_tarski(sK4) != sK4
    | sK4 = k3_tarski(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_1422,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2559,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X1))
    | k3_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_2561,plain,
    ( v3_ordinal1(k3_tarski(sK4))
    | ~ v3_ordinal1(sK4)
    | k3_tarski(sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_2559])).

cnf(c_18,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2508,plain,
    ( v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
    | ~ v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2487,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2090,plain,
    ( v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2091,plain,
    ( v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_233,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_449,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | k3_tarski(X0) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_24])).

cnf(c_450,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | k3_tarski(sK4) != sK4 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_439,plain,
    ( r2_hidden(sK5,sK4)
    | k3_tarski(X0) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_25])).

cnf(c_440,plain,
    ( r2_hidden(sK5,sK4)
    | k3_tarski(sK4) != sK4 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK5)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_429,plain,
    ( v3_ordinal1(sK5)
    | k3_tarski(X0) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_26])).

cnf(c_430,plain,
    ( v3_ordinal1(sK5)
    | k3_tarski(sK4) != sK4 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_10,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_71,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_73,plain,
    ( k3_tarski(sK4) = sK4
    | v4_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_66,plain,
    ( ~ r1_ordinal1(sK4,sK4)
    | r1_tarski(sK4,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_62,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_56,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
    | r2_hidden(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_52,plain,
    ( v3_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_40,plain,
    ( r1_ordinal1(sK4,sK4)
    | ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_35,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) != iProver_top
    | v4_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | v4_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33,plain,
    ( v3_ordinal1(sK5) = iProver_top
    | v4_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_151992,c_109027,c_108965,c_104524,c_102089,c_93885,c_91937,c_47744,c_44868,c_42319,c_38274,c_38270,c_38262,c_28546,c_28008,c_18993,c_17163,c_8442,c_8269,c_8258,c_8229,c_7082,c_4967,c_4569,c_4209,c_3143,c_2969,c_2920,c_2793,c_2561,c_2508,c_2487,c_2091,c_2090,c_450,c_440,c_430,c_73,c_66,c_62,c_56,c_52,c_40,c_37,c_35,c_34,c_33,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.73/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.73/7.00  
% 51.73/7.00  ------  iProver source info
% 51.73/7.00  
% 51.73/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.73/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.73/7.00  git: non_committed_changes: false
% 51.73/7.00  git: last_make_outside_of_git: false
% 51.73/7.00  
% 51.73/7.00  ------ 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options
% 51.73/7.00  
% 51.73/7.00  --out_options                           all
% 51.73/7.00  --tptp_safe_out                         true
% 51.73/7.00  --problem_path                          ""
% 51.73/7.00  --include_path                          ""
% 51.73/7.00  --clausifier                            res/vclausify_rel
% 51.73/7.00  --clausifier_options                    ""
% 51.73/7.00  --stdin                                 false
% 51.73/7.00  --stats_out                             all
% 51.73/7.00  
% 51.73/7.00  ------ General Options
% 51.73/7.00  
% 51.73/7.00  --fof                                   false
% 51.73/7.00  --time_out_real                         305.
% 51.73/7.00  --time_out_virtual                      -1.
% 51.73/7.00  --symbol_type_check                     false
% 51.73/7.00  --clausify_out                          false
% 51.73/7.00  --sig_cnt_out                           false
% 51.73/7.00  --trig_cnt_out                          false
% 51.73/7.00  --trig_cnt_out_tolerance                1.
% 51.73/7.00  --trig_cnt_out_sk_spl                   false
% 51.73/7.00  --abstr_cl_out                          false
% 51.73/7.00  
% 51.73/7.00  ------ Global Options
% 51.73/7.00  
% 51.73/7.00  --schedule                              default
% 51.73/7.00  --add_important_lit                     false
% 51.73/7.00  --prop_solver_per_cl                    1000
% 51.73/7.00  --min_unsat_core                        false
% 51.73/7.00  --soft_assumptions                      false
% 51.73/7.00  --soft_lemma_size                       3
% 51.73/7.00  --prop_impl_unit_size                   0
% 51.73/7.00  --prop_impl_unit                        []
% 51.73/7.00  --share_sel_clauses                     true
% 51.73/7.00  --reset_solvers                         false
% 51.73/7.00  --bc_imp_inh                            [conj_cone]
% 51.73/7.00  --conj_cone_tolerance                   3.
% 51.73/7.00  --extra_neg_conj                        none
% 51.73/7.00  --large_theory_mode                     true
% 51.73/7.00  --prolific_symb_bound                   200
% 51.73/7.00  --lt_threshold                          2000
% 51.73/7.00  --clause_weak_htbl                      true
% 51.73/7.00  --gc_record_bc_elim                     false
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing Options
% 51.73/7.00  
% 51.73/7.00  --preprocessing_flag                    true
% 51.73/7.00  --time_out_prep_mult                    0.1
% 51.73/7.00  --splitting_mode                        input
% 51.73/7.00  --splitting_grd                         true
% 51.73/7.00  --splitting_cvd                         false
% 51.73/7.00  --splitting_cvd_svl                     false
% 51.73/7.00  --splitting_nvd                         32
% 51.73/7.00  --sub_typing                            true
% 51.73/7.00  --prep_gs_sim                           true
% 51.73/7.00  --prep_unflatten                        true
% 51.73/7.00  --prep_res_sim                          true
% 51.73/7.00  --prep_upred                            true
% 51.73/7.00  --prep_sem_filter                       exhaustive
% 51.73/7.00  --prep_sem_filter_out                   false
% 51.73/7.00  --pred_elim                             true
% 51.73/7.00  --res_sim_input                         true
% 51.73/7.00  --eq_ax_congr_red                       true
% 51.73/7.00  --pure_diseq_elim                       true
% 51.73/7.00  --brand_transform                       false
% 51.73/7.00  --non_eq_to_eq                          false
% 51.73/7.00  --prep_def_merge                        true
% 51.73/7.00  --prep_def_merge_prop_impl              false
% 51.73/7.00  --prep_def_merge_mbd                    true
% 51.73/7.00  --prep_def_merge_tr_red                 false
% 51.73/7.00  --prep_def_merge_tr_cl                  false
% 51.73/7.00  --smt_preprocessing                     true
% 51.73/7.00  --smt_ac_axioms                         fast
% 51.73/7.00  --preprocessed_out                      false
% 51.73/7.00  --preprocessed_stats                    false
% 51.73/7.00  
% 51.73/7.00  ------ Abstraction refinement Options
% 51.73/7.00  
% 51.73/7.00  --abstr_ref                             []
% 51.73/7.00  --abstr_ref_prep                        false
% 51.73/7.00  --abstr_ref_until_sat                   false
% 51.73/7.00  --abstr_ref_sig_restrict                funpre
% 51.73/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.73/7.00  --abstr_ref_under                       []
% 51.73/7.00  
% 51.73/7.00  ------ SAT Options
% 51.73/7.00  
% 51.73/7.00  --sat_mode                              false
% 51.73/7.00  --sat_fm_restart_options                ""
% 51.73/7.00  --sat_gr_def                            false
% 51.73/7.00  --sat_epr_types                         true
% 51.73/7.00  --sat_non_cyclic_types                  false
% 51.73/7.00  --sat_finite_models                     false
% 51.73/7.00  --sat_fm_lemmas                         false
% 51.73/7.00  --sat_fm_prep                           false
% 51.73/7.00  --sat_fm_uc_incr                        true
% 51.73/7.00  --sat_out_model                         small
% 51.73/7.00  --sat_out_clauses                       false
% 51.73/7.00  
% 51.73/7.00  ------ QBF Options
% 51.73/7.00  
% 51.73/7.00  --qbf_mode                              false
% 51.73/7.00  --qbf_elim_univ                         false
% 51.73/7.00  --qbf_dom_inst                          none
% 51.73/7.00  --qbf_dom_pre_inst                      false
% 51.73/7.00  --qbf_sk_in                             false
% 51.73/7.00  --qbf_pred_elim                         true
% 51.73/7.00  --qbf_split                             512
% 51.73/7.00  
% 51.73/7.00  ------ BMC1 Options
% 51.73/7.00  
% 51.73/7.00  --bmc1_incremental                      false
% 51.73/7.00  --bmc1_axioms                           reachable_all
% 51.73/7.00  --bmc1_min_bound                        0
% 51.73/7.00  --bmc1_max_bound                        -1
% 51.73/7.00  --bmc1_max_bound_default                -1
% 51.73/7.00  --bmc1_symbol_reachability              true
% 51.73/7.00  --bmc1_property_lemmas                  false
% 51.73/7.00  --bmc1_k_induction                      false
% 51.73/7.00  --bmc1_non_equiv_states                 false
% 51.73/7.00  --bmc1_deadlock                         false
% 51.73/7.00  --bmc1_ucm                              false
% 51.73/7.00  --bmc1_add_unsat_core                   none
% 51.73/7.00  --bmc1_unsat_core_children              false
% 51.73/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.73/7.00  --bmc1_out_stat                         full
% 51.73/7.00  --bmc1_ground_init                      false
% 51.73/7.00  --bmc1_pre_inst_next_state              false
% 51.73/7.00  --bmc1_pre_inst_state                   false
% 51.73/7.00  --bmc1_pre_inst_reach_state             false
% 51.73/7.00  --bmc1_out_unsat_core                   false
% 51.73/7.00  --bmc1_aig_witness_out                  false
% 51.73/7.00  --bmc1_verbose                          false
% 51.73/7.00  --bmc1_dump_clauses_tptp                false
% 51.73/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.73/7.00  --bmc1_dump_file                        -
% 51.73/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.73/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.73/7.00  --bmc1_ucm_extend_mode                  1
% 51.73/7.00  --bmc1_ucm_init_mode                    2
% 51.73/7.00  --bmc1_ucm_cone_mode                    none
% 51.73/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.73/7.00  --bmc1_ucm_relax_model                  4
% 51.73/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.73/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.73/7.00  --bmc1_ucm_layered_model                none
% 51.73/7.00  --bmc1_ucm_max_lemma_size               10
% 51.73/7.00  
% 51.73/7.00  ------ AIG Options
% 51.73/7.00  
% 51.73/7.00  --aig_mode                              false
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation Options
% 51.73/7.00  
% 51.73/7.00  --instantiation_flag                    true
% 51.73/7.00  --inst_sos_flag                         true
% 51.73/7.00  --inst_sos_phase                        true
% 51.73/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel_side                     num_symb
% 51.73/7.00  --inst_solver_per_active                1400
% 51.73/7.00  --inst_solver_calls_frac                1.
% 51.73/7.00  --inst_passive_queue_type               priority_queues
% 51.73/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.73/7.00  --inst_passive_queues_freq              [25;2]
% 51.73/7.00  --inst_dismatching                      true
% 51.73/7.00  --inst_eager_unprocessed_to_passive     true
% 51.73/7.00  --inst_prop_sim_given                   true
% 51.73/7.00  --inst_prop_sim_new                     false
% 51.73/7.00  --inst_subs_new                         false
% 51.73/7.00  --inst_eq_res_simp                      false
% 51.73/7.00  --inst_subs_given                       false
% 51.73/7.00  --inst_orphan_elimination               true
% 51.73/7.00  --inst_learning_loop_flag               true
% 51.73/7.00  --inst_learning_start                   3000
% 51.73/7.00  --inst_learning_factor                  2
% 51.73/7.00  --inst_start_prop_sim_after_learn       3
% 51.73/7.00  --inst_sel_renew                        solver
% 51.73/7.00  --inst_lit_activity_flag                true
% 51.73/7.00  --inst_restr_to_given                   false
% 51.73/7.00  --inst_activity_threshold               500
% 51.73/7.00  --inst_out_proof                        true
% 51.73/7.00  
% 51.73/7.00  ------ Resolution Options
% 51.73/7.00  
% 51.73/7.00  --resolution_flag                       true
% 51.73/7.00  --res_lit_sel                           adaptive
% 51.73/7.00  --res_lit_sel_side                      none
% 51.73/7.00  --res_ordering                          kbo
% 51.73/7.00  --res_to_prop_solver                    active
% 51.73/7.00  --res_prop_simpl_new                    false
% 51.73/7.00  --res_prop_simpl_given                  true
% 51.73/7.00  --res_passive_queue_type                priority_queues
% 51.73/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.73/7.00  --res_passive_queues_freq               [15;5]
% 51.73/7.00  --res_forward_subs                      full
% 51.73/7.00  --res_backward_subs                     full
% 51.73/7.00  --res_forward_subs_resolution           true
% 51.73/7.00  --res_backward_subs_resolution          true
% 51.73/7.00  --res_orphan_elimination                true
% 51.73/7.00  --res_time_limit                        2.
% 51.73/7.00  --res_out_proof                         true
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Options
% 51.73/7.00  
% 51.73/7.00  --superposition_flag                    true
% 51.73/7.00  --sup_passive_queue_type                priority_queues
% 51.73/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.73/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.73/7.00  --demod_completeness_check              fast
% 51.73/7.00  --demod_use_ground                      true
% 51.73/7.00  --sup_to_prop_solver                    passive
% 51.73/7.00  --sup_prop_simpl_new                    true
% 51.73/7.00  --sup_prop_simpl_given                  true
% 51.73/7.00  --sup_fun_splitting                     true
% 51.73/7.00  --sup_smt_interval                      50000
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Simplification Setup
% 51.73/7.00  
% 51.73/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.73/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.73/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_immed_triv                        [TrivRules]
% 51.73/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_bw_main                     []
% 51.73/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.73/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_input_bw                          []
% 51.73/7.00  
% 51.73/7.00  ------ Combination Options
% 51.73/7.00  
% 51.73/7.00  --comb_res_mult                         3
% 51.73/7.00  --comb_sup_mult                         2
% 51.73/7.00  --comb_inst_mult                        10
% 51.73/7.00  
% 51.73/7.00  ------ Debug Options
% 51.73/7.00  
% 51.73/7.00  --dbg_backtrace                         false
% 51.73/7.00  --dbg_dump_prop_clauses                 false
% 51.73/7.00  --dbg_dump_prop_clauses_file            -
% 51.73/7.00  --dbg_out_stat                          false
% 51.73/7.00  ------ Parsing...
% 51.73/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.73/7.00  ------ Proving...
% 51.73/7.00  ------ Problem Properties 
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  clauses                                 28
% 51.73/7.00  conjectures                             5
% 51.73/7.00  EPR                                     8
% 51.73/7.00  Horn                                    23
% 51.73/7.00  unary                                   2
% 51.73/7.00  binary                                  12
% 51.73/7.00  lits                                    75
% 51.73/7.00  lits eq                                 6
% 51.73/7.00  fd_pure                                 0
% 51.73/7.00  fd_pseudo                               0
% 51.73/7.00  fd_cond                                 0
% 51.73/7.00  fd_pseudo_cond                          4
% 51.73/7.00  AC symbols                              0
% 51.73/7.00  
% 51.73/7.00  ------ Schedule dynamic 5 is on 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  ------ 
% 51.73/7.00  Current options:
% 51.73/7.00  ------ 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options
% 51.73/7.00  
% 51.73/7.00  --out_options                           all
% 51.73/7.00  --tptp_safe_out                         true
% 51.73/7.00  --problem_path                          ""
% 51.73/7.00  --include_path                          ""
% 51.73/7.00  --clausifier                            res/vclausify_rel
% 51.73/7.00  --clausifier_options                    ""
% 51.73/7.00  --stdin                                 false
% 51.73/7.00  --stats_out                             all
% 51.73/7.00  
% 51.73/7.00  ------ General Options
% 51.73/7.00  
% 51.73/7.00  --fof                                   false
% 51.73/7.00  --time_out_real                         305.
% 51.73/7.00  --time_out_virtual                      -1.
% 51.73/7.00  --symbol_type_check                     false
% 51.73/7.00  --clausify_out                          false
% 51.73/7.00  --sig_cnt_out                           false
% 51.73/7.00  --trig_cnt_out                          false
% 51.73/7.00  --trig_cnt_out_tolerance                1.
% 51.73/7.00  --trig_cnt_out_sk_spl                   false
% 51.73/7.00  --abstr_cl_out                          false
% 51.73/7.00  
% 51.73/7.00  ------ Global Options
% 51.73/7.00  
% 51.73/7.00  --schedule                              default
% 51.73/7.00  --add_important_lit                     false
% 51.73/7.00  --prop_solver_per_cl                    1000
% 51.73/7.00  --min_unsat_core                        false
% 51.73/7.00  --soft_assumptions                      false
% 51.73/7.00  --soft_lemma_size                       3
% 51.73/7.00  --prop_impl_unit_size                   0
% 51.73/7.00  --prop_impl_unit                        []
% 51.73/7.00  --share_sel_clauses                     true
% 51.73/7.00  --reset_solvers                         false
% 51.73/7.00  --bc_imp_inh                            [conj_cone]
% 51.73/7.00  --conj_cone_tolerance                   3.
% 51.73/7.00  --extra_neg_conj                        none
% 51.73/7.00  --large_theory_mode                     true
% 51.73/7.00  --prolific_symb_bound                   200
% 51.73/7.00  --lt_threshold                          2000
% 51.73/7.00  --clause_weak_htbl                      true
% 51.73/7.00  --gc_record_bc_elim                     false
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing Options
% 51.73/7.00  
% 51.73/7.00  --preprocessing_flag                    true
% 51.73/7.00  --time_out_prep_mult                    0.1
% 51.73/7.00  --splitting_mode                        input
% 51.73/7.00  --splitting_grd                         true
% 51.73/7.00  --splitting_cvd                         false
% 51.73/7.00  --splitting_cvd_svl                     false
% 51.73/7.00  --splitting_nvd                         32
% 51.73/7.00  --sub_typing                            true
% 51.73/7.00  --prep_gs_sim                           true
% 51.73/7.00  --prep_unflatten                        true
% 51.73/7.00  --prep_res_sim                          true
% 51.73/7.00  --prep_upred                            true
% 51.73/7.00  --prep_sem_filter                       exhaustive
% 51.73/7.00  --prep_sem_filter_out                   false
% 51.73/7.00  --pred_elim                             true
% 51.73/7.00  --res_sim_input                         true
% 51.73/7.00  --eq_ax_congr_red                       true
% 51.73/7.00  --pure_diseq_elim                       true
% 51.73/7.00  --brand_transform                       false
% 51.73/7.00  --non_eq_to_eq                          false
% 51.73/7.00  --prep_def_merge                        true
% 51.73/7.00  --prep_def_merge_prop_impl              false
% 51.73/7.00  --prep_def_merge_mbd                    true
% 51.73/7.00  --prep_def_merge_tr_red                 false
% 51.73/7.00  --prep_def_merge_tr_cl                  false
% 51.73/7.00  --smt_preprocessing                     true
% 51.73/7.00  --smt_ac_axioms                         fast
% 51.73/7.00  --preprocessed_out                      false
% 51.73/7.00  --preprocessed_stats                    false
% 51.73/7.00  
% 51.73/7.00  ------ Abstraction refinement Options
% 51.73/7.00  
% 51.73/7.00  --abstr_ref                             []
% 51.73/7.00  --abstr_ref_prep                        false
% 51.73/7.00  --abstr_ref_until_sat                   false
% 51.73/7.00  --abstr_ref_sig_restrict                funpre
% 51.73/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.73/7.00  --abstr_ref_under                       []
% 51.73/7.00  
% 51.73/7.00  ------ SAT Options
% 51.73/7.00  
% 51.73/7.00  --sat_mode                              false
% 51.73/7.00  --sat_fm_restart_options                ""
% 51.73/7.00  --sat_gr_def                            false
% 51.73/7.00  --sat_epr_types                         true
% 51.73/7.00  --sat_non_cyclic_types                  false
% 51.73/7.00  --sat_finite_models                     false
% 51.73/7.00  --sat_fm_lemmas                         false
% 51.73/7.00  --sat_fm_prep                           false
% 51.73/7.00  --sat_fm_uc_incr                        true
% 51.73/7.00  --sat_out_model                         small
% 51.73/7.00  --sat_out_clauses                       false
% 51.73/7.00  
% 51.73/7.00  ------ QBF Options
% 51.73/7.00  
% 51.73/7.00  --qbf_mode                              false
% 51.73/7.00  --qbf_elim_univ                         false
% 51.73/7.00  --qbf_dom_inst                          none
% 51.73/7.00  --qbf_dom_pre_inst                      false
% 51.73/7.00  --qbf_sk_in                             false
% 51.73/7.00  --qbf_pred_elim                         true
% 51.73/7.00  --qbf_split                             512
% 51.73/7.00  
% 51.73/7.00  ------ BMC1 Options
% 51.73/7.00  
% 51.73/7.00  --bmc1_incremental                      false
% 51.73/7.00  --bmc1_axioms                           reachable_all
% 51.73/7.00  --bmc1_min_bound                        0
% 51.73/7.00  --bmc1_max_bound                        -1
% 51.73/7.00  --bmc1_max_bound_default                -1
% 51.73/7.00  --bmc1_symbol_reachability              true
% 51.73/7.00  --bmc1_property_lemmas                  false
% 51.73/7.00  --bmc1_k_induction                      false
% 51.73/7.00  --bmc1_non_equiv_states                 false
% 51.73/7.00  --bmc1_deadlock                         false
% 51.73/7.00  --bmc1_ucm                              false
% 51.73/7.00  --bmc1_add_unsat_core                   none
% 51.73/7.00  --bmc1_unsat_core_children              false
% 51.73/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.73/7.00  --bmc1_out_stat                         full
% 51.73/7.00  --bmc1_ground_init                      false
% 51.73/7.00  --bmc1_pre_inst_next_state              false
% 51.73/7.00  --bmc1_pre_inst_state                   false
% 51.73/7.00  --bmc1_pre_inst_reach_state             false
% 51.73/7.00  --bmc1_out_unsat_core                   false
% 51.73/7.00  --bmc1_aig_witness_out                  false
% 51.73/7.00  --bmc1_verbose                          false
% 51.73/7.00  --bmc1_dump_clauses_tptp                false
% 51.73/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.73/7.00  --bmc1_dump_file                        -
% 51.73/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.73/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.73/7.00  --bmc1_ucm_extend_mode                  1
% 51.73/7.00  --bmc1_ucm_init_mode                    2
% 51.73/7.00  --bmc1_ucm_cone_mode                    none
% 51.73/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.73/7.00  --bmc1_ucm_relax_model                  4
% 51.73/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.73/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.73/7.00  --bmc1_ucm_layered_model                none
% 51.73/7.00  --bmc1_ucm_max_lemma_size               10
% 51.73/7.00  
% 51.73/7.00  ------ AIG Options
% 51.73/7.00  
% 51.73/7.00  --aig_mode                              false
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation Options
% 51.73/7.00  
% 51.73/7.00  --instantiation_flag                    true
% 51.73/7.00  --inst_sos_flag                         true
% 51.73/7.00  --inst_sos_phase                        true
% 51.73/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel_side                     none
% 51.73/7.00  --inst_solver_per_active                1400
% 51.73/7.00  --inst_solver_calls_frac                1.
% 51.73/7.00  --inst_passive_queue_type               priority_queues
% 51.73/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.73/7.00  --inst_passive_queues_freq              [25;2]
% 51.73/7.00  --inst_dismatching                      true
% 51.73/7.00  --inst_eager_unprocessed_to_passive     true
% 51.73/7.00  --inst_prop_sim_given                   true
% 51.73/7.00  --inst_prop_sim_new                     false
% 51.73/7.00  --inst_subs_new                         false
% 51.73/7.00  --inst_eq_res_simp                      false
% 51.73/7.00  --inst_subs_given                       false
% 51.73/7.00  --inst_orphan_elimination               true
% 51.73/7.00  --inst_learning_loop_flag               true
% 51.73/7.00  --inst_learning_start                   3000
% 51.73/7.00  --inst_learning_factor                  2
% 51.73/7.00  --inst_start_prop_sim_after_learn       3
% 51.73/7.00  --inst_sel_renew                        solver
% 51.73/7.00  --inst_lit_activity_flag                true
% 51.73/7.00  --inst_restr_to_given                   false
% 51.73/7.00  --inst_activity_threshold               500
% 51.73/7.00  --inst_out_proof                        true
% 51.73/7.00  
% 51.73/7.00  ------ Resolution Options
% 51.73/7.00  
% 51.73/7.00  --resolution_flag                       false
% 51.73/7.00  --res_lit_sel                           adaptive
% 51.73/7.00  --res_lit_sel_side                      none
% 51.73/7.00  --res_ordering                          kbo
% 51.73/7.00  --res_to_prop_solver                    active
% 51.73/7.00  --res_prop_simpl_new                    false
% 51.73/7.00  --res_prop_simpl_given                  true
% 51.73/7.00  --res_passive_queue_type                priority_queues
% 51.73/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.73/7.00  --res_passive_queues_freq               [15;5]
% 51.73/7.00  --res_forward_subs                      full
% 51.73/7.00  --res_backward_subs                     full
% 51.73/7.00  --res_forward_subs_resolution           true
% 51.73/7.00  --res_backward_subs_resolution          true
% 51.73/7.00  --res_orphan_elimination                true
% 51.73/7.00  --res_time_limit                        2.
% 51.73/7.00  --res_out_proof                         true
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Options
% 51.73/7.00  
% 51.73/7.00  --superposition_flag                    true
% 51.73/7.00  --sup_passive_queue_type                priority_queues
% 51.73/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.73/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.73/7.00  --demod_completeness_check              fast
% 51.73/7.00  --demod_use_ground                      true
% 51.73/7.00  --sup_to_prop_solver                    passive
% 51.73/7.00  --sup_prop_simpl_new                    true
% 51.73/7.00  --sup_prop_simpl_given                  true
% 51.73/7.00  --sup_fun_splitting                     true
% 51.73/7.00  --sup_smt_interval                      50000
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Simplification Setup
% 51.73/7.00  
% 51.73/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.73/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.73/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_immed_triv                        [TrivRules]
% 51.73/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_bw_main                     []
% 51.73/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.73/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_input_bw                          []
% 51.73/7.00  
% 51.73/7.00  ------ Combination Options
% 51.73/7.00  
% 51.73/7.00  --comb_res_mult                         3
% 51.73/7.00  --comb_sup_mult                         2
% 51.73/7.00  --comb_inst_mult                        10
% 51.73/7.00  
% 51.73/7.00  ------ Debug Options
% 51.73/7.00  
% 51.73/7.00  --dbg_backtrace                         false
% 51.73/7.00  --dbg_dump_prop_clauses                 false
% 51.73/7.00  --dbg_dump_prop_clauses_file            -
% 51.73/7.00  --dbg_out_stat                          false
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  ------ Proving...
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  % SZS status Theorem for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  fof(f6,axiom,(
% 51.73/7.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f17,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 51.73/7.00    inference(ennf_transformation,[],[f6])).
% 51.73/7.00  
% 51.73/7.00  fof(f18,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(flattening,[],[f17])).
% 51.73/7.00  
% 51.73/7.00  fof(f38,plain,(
% 51.73/7.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(nnf_transformation,[],[f18])).
% 51.73/7.00  
% 51.73/7.00  fof(f61,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f38])).
% 51.73/7.00  
% 51.73/7.00  fof(f12,axiom,(
% 51.73/7.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f23,plain,(
% 51.73/7.00    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(ennf_transformation,[],[f12])).
% 51.73/7.00  
% 51.73/7.00  fof(f42,plain,(
% 51.73/7.00    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(nnf_transformation,[],[f23])).
% 51.73/7.00  
% 51.73/7.00  fof(f71,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f42])).
% 51.73/7.00  
% 51.73/7.00  fof(f3,axiom,(
% 51.73/7.00    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f58,plain,(
% 51.73/7.00    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 51.73/7.00    inference(cnf_transformation,[],[f3])).
% 51.73/7.00  
% 51.73/7.00  fof(f87,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f71,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f13,axiom,(
% 51.73/7.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f24,plain,(
% 51.73/7.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 51.73/7.00    inference(ennf_transformation,[],[f13])).
% 51.73/7.00  
% 51.73/7.00  fof(f73,plain,(
% 51.73/7.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f24])).
% 51.73/7.00  
% 51.73/7.00  fof(f1,axiom,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f16,plain,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.73/7.00    inference(ennf_transformation,[],[f1])).
% 51.73/7.00  
% 51.73/7.00  fof(f27,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(nnf_transformation,[],[f16])).
% 51.73/7.00  
% 51.73/7.00  fof(f28,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(rectify,[],[f27])).
% 51.73/7.00  
% 51.73/7.00  fof(f29,plain,(
% 51.73/7.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f30,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 51.73/7.00  
% 51.73/7.00  fof(f49,plain,(
% 51.73/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f30])).
% 51.73/7.00  
% 51.73/7.00  fof(f2,axiom,(
% 51.73/7.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f31,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(nnf_transformation,[],[f2])).
% 51.73/7.00  
% 51.73/7.00  fof(f32,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(rectify,[],[f31])).
% 51.73/7.00  
% 51.73/7.00  fof(f35,plain,(
% 51.73/7.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f34,plain,(
% 51.73/7.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f33,plain,(
% 51.73/7.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f36,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 51.73/7.00  
% 51.73/7.00  fof(f56,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f14,conjecture,(
% 51.73/7.00    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f15,negated_conjecture,(
% 51.73/7.00    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 51.73/7.00    inference(negated_conjecture,[],[f14])).
% 51.73/7.00  
% 51.73/7.00  fof(f25,plain,(
% 51.73/7.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 51.73/7.00    inference(ennf_transformation,[],[f15])).
% 51.73/7.00  
% 51.73/7.00  fof(f26,plain,(
% 51.73/7.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 51.73/7.00    inference(flattening,[],[f25])).
% 51.73/7.00  
% 51.73/7.00  fof(f43,plain,(
% 51.73/7.00    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 51.73/7.00    inference(nnf_transformation,[],[f26])).
% 51.73/7.00  
% 51.73/7.00  fof(f44,plain,(
% 51.73/7.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 51.73/7.00    inference(flattening,[],[f43])).
% 51.73/7.00  
% 51.73/7.00  fof(f45,plain,(
% 51.73/7.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 51.73/7.00    inference(rectify,[],[f44])).
% 51.73/7.00  
% 51.73/7.00  fof(f47,plain,(
% 51.73/7.00    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK5),X0) & r2_hidden(sK5,X0) & v3_ordinal1(sK5))) )),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f46,plain,(
% 51.73/7.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK4) & r2_hidden(X1,sK4) & v3_ordinal1(X1)) | ~v4_ordinal1(sK4)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) | v4_ordinal1(sK4)) & v3_ordinal1(sK4))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f48,plain,(
% 51.73/7.00    ((~r2_hidden(k1_ordinal1(sK5),sK4) & r2_hidden(sK5,sK4) & v3_ordinal1(sK5)) | ~v4_ordinal1(sK4)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) | v4_ordinal1(sK4)) & v3_ordinal1(sK4)),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).
% 51.73/7.00  
% 51.73/7.00  fof(f75,plain,(
% 51.73/7.00    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2) | v4_ordinal1(sK4)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f48])).
% 51.73/7.00  
% 51.73/7.00  fof(f89,plain,(
% 51.73/7.00    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2) | v4_ordinal1(sK4)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f75,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f7,axiom,(
% 51.73/7.00    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f63,plain,(
% 51.73/7.00    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 51.73/7.00    inference(cnf_transformation,[],[f7])).
% 51.73/7.00  
% 51.73/7.00  fof(f79,plain,(
% 51.73/7.00    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 51.73/7.00    inference(definition_unfolding,[],[f63,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f57,plain,(
% 51.73/7.00    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f74,plain,(
% 51.73/7.00    v3_ordinal1(sK4)),
% 51.73/7.00    inference(cnf_transformation,[],[f48])).
% 51.73/7.00  
% 51.73/7.00  fof(f5,axiom,(
% 51.73/7.00    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f37,plain,(
% 51.73/7.00    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 51.73/7.00    inference(nnf_transformation,[],[f5])).
% 51.73/7.00  
% 51.73/7.00  fof(f60,plain,(
% 51.73/7.00    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 51.73/7.00    inference(cnf_transformation,[],[f37])).
% 51.73/7.00  
% 51.73/7.00  fof(f55,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(sK1(X0,X1),X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f9,axiom,(
% 51.73/7.00    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f19,plain,(
% 51.73/7.00    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 51.73/7.00    inference(ennf_transformation,[],[f9])).
% 51.73/7.00  
% 51.73/7.00  fof(f20,plain,(
% 51.73/7.00    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 51.73/7.00    inference(flattening,[],[f19])).
% 51.73/7.00  
% 51.73/7.00  fof(f67,plain,(
% 51.73/7.00    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f20])).
% 51.73/7.00  
% 51.73/7.00  fof(f8,axiom,(
% 51.73/7.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f39,plain,(
% 51.73/7.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 51.73/7.00    inference(nnf_transformation,[],[f8])).
% 51.73/7.00  
% 51.73/7.00  fof(f40,plain,(
% 51.73/7.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 51.73/7.00    inference(flattening,[],[f39])).
% 51.73/7.00  
% 51.73/7.00  fof(f65,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f40])).
% 51.73/7.00  
% 51.73/7.00  fof(f81,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f65,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f52,plain,(
% 51.73/7.00    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f92,plain,(
% 51.73/7.00    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 51.73/7.00    inference(equality_resolution,[],[f52])).
% 51.73/7.00  
% 51.73/7.00  fof(f53,plain,(
% 51.73/7.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f91,plain,(
% 51.73/7.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 51.73/7.00    inference(equality_resolution,[],[f53])).
% 51.73/7.00  
% 51.73/7.00  fof(f11,axiom,(
% 51.73/7.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f22,plain,(
% 51.73/7.00    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(ennf_transformation,[],[f11])).
% 51.73/7.00  
% 51.73/7.00  fof(f41,plain,(
% 51.73/7.00    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(nnf_transformation,[],[f22])).
% 51.73/7.00  
% 51.73/7.00  fof(f69,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f41])).
% 51.73/7.00  
% 51.73/7.00  fof(f85,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f69,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f64,plain,(
% 51.73/7.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 51.73/7.00    inference(cnf_transformation,[],[f40])).
% 51.73/7.00  
% 51.73/7.00  fof(f82,plain,(
% 51.73/7.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 51.73/7.00    inference(definition_unfolding,[],[f64,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f72,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f42])).
% 51.73/7.00  
% 51.73/7.00  fof(f86,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f72,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f10,axiom,(
% 51.73/7.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 51.73/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f21,plain,(
% 51.73/7.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 51.73/7.00    inference(ennf_transformation,[],[f10])).
% 51.73/7.00  
% 51.73/7.00  fof(f68,plain,(
% 51.73/7.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f21])).
% 51.73/7.00  
% 51.73/7.00  fof(f83,plain,(
% 51.73/7.00    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f68,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f78,plain,(
% 51.73/7.00    ~r2_hidden(k1_ordinal1(sK5),sK4) | ~v4_ordinal1(sK4)),
% 51.73/7.00    inference(cnf_transformation,[],[f48])).
% 51.73/7.00  
% 51.73/7.00  fof(f88,plain,(
% 51.73/7.00    ~r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) | ~v4_ordinal1(sK4)),
% 51.73/7.00    inference(definition_unfolding,[],[f78,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f77,plain,(
% 51.73/7.00    r2_hidden(sK5,sK4) | ~v4_ordinal1(sK4)),
% 51.73/7.00    inference(cnf_transformation,[],[f48])).
% 51.73/7.00  
% 51.73/7.00  fof(f76,plain,(
% 51.73/7.00    v3_ordinal1(sK5) | ~v4_ordinal1(sK4)),
% 51.73/7.00    inference(cnf_transformation,[],[f48])).
% 51.73/7.00  
% 51.73/7.00  fof(f59,plain,(
% 51.73/7.00    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f37])).
% 51.73/7.00  
% 51.73/7.00  fof(f66,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 51.73/7.00    inference(cnf_transformation,[],[f40])).
% 51.73/7.00  
% 51.73/7.00  fof(f80,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 51.73/7.00    inference(definition_unfolding,[],[f66,f58])).
% 51.73/7.00  
% 51.73/7.00  fof(f93,plain,(
% 51.73/7.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 51.73/7.00    inference(equality_resolution,[],[f80])).
% 51.73/7.00  
% 51.73/7.00  cnf(c_12,plain,
% 51.73/7.00      ( ~ r1_ordinal1(X0,X1)
% 51.73/7.00      | r1_tarski(X0,X1)
% 51.73/7.00      | ~ v3_ordinal1(X1)
% 51.73/7.00      | ~ v3_ordinal1(X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f61]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_91950,plain,
% 51.73/7.00      ( ~ r1_ordinal1(X0,sK5)
% 51.73/7.00      | r1_tarski(X0,sK5)
% 51.73/7.00      | ~ v3_ordinal1(X0)
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_151992,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK3(sK4,sK5),sK5)
% 51.73/7.00      | r1_tarski(sK3(sK4,sK5),sK5)
% 51.73/7.00      | ~ v3_ordinal1(sK3(sK4,sK5))
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_91950]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_22,plain,
% 51.73/7.00      ( r1_ordinal1(X0,X1)
% 51.73/7.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | ~ v3_ordinal1(X1)
% 51.73/7.00      | ~ v3_ordinal1(X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f87]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_90051,plain,
% 51.73/7.00      ( r1_ordinal1(X0,sK5)
% 51.73/7.00      | ~ r2_hidden(X0,k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | ~ v3_ordinal1(X0)
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_109027,plain,
% 51.73/7.00      ( r1_ordinal1(sK3(sK4,sK5),sK5)
% 51.73/7.00      | ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | ~ v3_ordinal1(sK3(sK4,sK5))
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_90051]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1419,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.73/7.00      theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_89143,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) != X0
% 51.73/7.00      | sK4 != X1 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1419]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_108963,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | ~ r2_hidden(sK3(sK4,sK5),X0)
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) != sK3(sK4,sK5)
% 51.73/7.00      | sK4 != X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_89143]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_108965,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | ~ r2_hidden(sK3(sK4,sK5),sK4)
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) != sK3(sK4,sK5)
% 51.73/7.00      | sK4 != sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_108963]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_23,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f73]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_90405,plain,
% 51.73/7.00      ( ~ r2_hidden(sK5,X0) | ~ r1_tarski(X0,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_104524,plain,
% 51.73/7.00      ( ~ r2_hidden(sK5,sK5) | ~ r1_tarski(sK5,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_90405]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_102089,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK5,sK5)
% 51.73/7.00      | r1_tarski(sK5,sK5)
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_91950]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 51.73/7.00      inference(cnf_transformation,[],[f49]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_89746,plain,
% 51.73/7.00      ( r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(X0,sK3(X2,X0))
% 51.73/7.00      | ~ r1_tarski(sK3(X2,X0),X1) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_90834,plain,
% 51.73/7.00      ( r2_hidden(sK5,X0)
% 51.73/7.00      | ~ r2_hidden(sK5,sK3(X1,sK5))
% 51.73/7.00      | ~ r1_tarski(sK3(X1,sK5),X0) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_89746]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_93878,plain,
% 51.73/7.00      ( ~ r2_hidden(sK5,sK3(X0,sK5))
% 51.73/7.00      | r2_hidden(sK5,sK5)
% 51.73/7.00      | ~ r1_tarski(sK3(X0,sK5),sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_90834]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_93885,plain,
% 51.73/7.00      ( ~ r2_hidden(sK5,sK3(sK4,sK5))
% 51.73/7.00      | r2_hidden(sK5,sK5)
% 51.73/7.00      | ~ r1_tarski(sK3(sK4,sK5),sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_93878]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_91937,plain,
% 51.73/7.00      ( r1_ordinal1(sK5,sK5)
% 51.73/7.00      | ~ r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_90051]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4,plain,
% 51.73/7.00      ( r2_hidden(sK2(X0,X1),X0)
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1)
% 51.73/7.00      | k3_tarski(X0) = X1 ),
% 51.73/7.00      inference(cnf_transformation,[],[f56]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2028,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2030,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r2_hidden(X0,X2) = iProver_top
% 51.73/7.00      | r1_tarski(X1,X2) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3835,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 51.73/7.00      | r1_tarski(X1,X2) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2028,c_2030]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_27,negated_conjecture,
% 51.73/7.00      ( ~ r2_hidden(X0,sK4)
% 51.73/7.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 51.73/7.00      | ~ v3_ordinal1(X0)
% 51.73/7.00      | v4_ordinal1(sK4) ),
% 51.73/7.00      inference(cnf_transformation,[],[f89]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2007,plain,
% 51.73/7.00      ( r2_hidden(X0,sK4) != iProver_top
% 51.73/7.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4) = iProver_top
% 51.73/7.00      | v3_ordinal1(X0) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_13,plain,
% 51.73/7.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 51.73/7.00      inference(cnf_transformation,[],[f79]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2019,plain,
% 51.73/7.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(sK1(X1,X2),X0)
% 51.73/7.00      | ~ r2_hidden(sK1(X1,X2),X2)
% 51.73/7.00      | k3_tarski(X1) = X2 ),
% 51.73/7.00      inference(cnf_transformation,[],[f57]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2029,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(X2,X0) != iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X2) != iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4734,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(X2,X0) != iProver_top
% 51.73/7.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X2) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2028,c_2029]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_46693,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK1(X0,X1),k1_tarski(sK1(X0,X1))),X0) != iProver_top
% 51.73/7.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2019,c_4734]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47436,plain,
% 51.73/7.00      ( k3_tarski(sK4) = X0
% 51.73/7.00      | r2_hidden(sK2(sK4,X0),sK4) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(sK4,X0),sK4) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,X0)) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2007,c_46693]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47656,plain,
% 51.73/7.00      ( k3_tarski(sK4) = X0
% 51.73/7.00      | r2_hidden(sK2(sK4,X0),sK4) = iProver_top
% 51.73/7.00      | r1_tarski(X0,sK4) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,X0)) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_3835,c_47436]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_28,negated_conjecture,
% 51.73/7.00      ( v3_ordinal1(sK4) ),
% 51.73/7.00      inference(cnf_transformation,[],[f74]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_29,plain,
% 51.73/7.00      ( v3_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_9,plain,
% 51.73/7.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 51.73/7.00      inference(cnf_transformation,[],[f60]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_74,plain,
% 51.73/7.00      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_76,plain,
% 51.73/7.00      ( k3_tarski(sK4) != sK4 | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_74]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2638,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4)
% 51.73/7.00      | ~ r2_hidden(sK1(sK4,sK4),sK4)
% 51.73/7.00      | ~ v3_ordinal1(sK1(sK4,sK4))
% 51.73/7.00      | v4_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_27]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2639,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(sK4,sK4),sK4) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,sK4)) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2638]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2341,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,sK4)
% 51.73/7.00      | ~ r2_hidden(sK1(sK4,sK4),X0)
% 51.73/7.00      | ~ r2_hidden(sK1(sK4,sK4),sK4)
% 51.73/7.00      | k3_tarski(sK4) = sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3249,plain,
% 51.73/7.00      ( ~ r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4)
% 51.73/7.00      | ~ r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))))
% 51.73/7.00      | ~ r2_hidden(sK1(sK4,sK4),sK4)
% 51.73/7.00      | k3_tarski(sK4) = sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2341]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3253,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4))),sK4) != iProver_top
% 51.73/7.00      | r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) != iProver_top
% 51.73/7.00      | r2_hidden(sK1(sK4,sK4),sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_3249]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_5,plain,
% 51.73/7.00      ( r2_hidden(sK1(X0,X1),X1)
% 51.73/7.00      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 51.73/7.00      | k3_tarski(X0) = X1 ),
% 51.73/7.00      inference(cnf_transformation,[],[f55]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2027,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),sK2(X0,X1)) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3951,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 51.73/7.00      | r1_tarski(sK2(X0,X1),X2) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2027,c_2030]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3958,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4
% 51.73/7.00      | r2_hidden(sK1(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | r1_tarski(sK2(sK4,sK4),sK4) != iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3951]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_5318,plain,
% 51.73/7.00      ( r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_5319,plain,
% 51.73/7.00      ( r2_hidden(sK1(sK4,sK4),k2_xboole_0(sK1(sK4,sK4),k1_tarski(sK1(sK4,sK4)))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_5318]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_9087,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK2(sK4,sK4),sK4)
% 51.73/7.00      | r1_tarski(sK2(sK4,sK4),sK4)
% 51.73/7.00      | ~ v3_ordinal1(sK2(sK4,sK4))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_9094,plain,
% 51.73/7.00      ( r1_ordinal1(sK2(sK4,sK4),sK4) != iProver_top
% 51.73/7.00      | r1_tarski(sK2(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK2(sK4,sK4)) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_9087]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_17,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f67]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2016,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X0) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3952,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK2(X0,X1)) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2027,c_2016]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_39068,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK2(X0,X1)) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_3952,c_2016]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_39107,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4
% 51.73/7.00      | v3_ordinal1(sK2(sK4,sK4)) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,sK4)) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_39068]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47668,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4
% 51.73/7.00      | r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,sK4)) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2028,c_47436]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3836,plain,
% 51.73/7.00      ( k3_tarski(X0) = X1
% 51.73/7.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(X0,X1)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2028,c_2016]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3851,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4
% 51.73/7.00      | r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK1(sK4,sK4)) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3836]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47676,plain,
% 51.73/7.00      ( r2_hidden(sK2(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(global_propositional_subsumption,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_47668,c_29,c_76,c_3851]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_15,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 51.73/7.00      inference(cnf_transformation,[],[f81]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2018,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2012,plain,
% 51.73/7.00      ( r1_ordinal1(X0,X1) = iProver_top
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 51.73/7.00      | v3_ordinal1(X0) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3062,plain,
% 51.73/7.00      ( r1_ordinal1(X0,X1) = iProver_top
% 51.73/7.00      | r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X0) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2018,c_2012]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_39,plain,
% 51.73/7.00      ( r1_ordinal1(X0,X1) = iProver_top
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 51.73/7.00      | v3_ordinal1(X0) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_54,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X0) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_58,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_7376,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r1_ordinal1(X0,X1) = iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top ),
% 51.73/7.00      inference(global_propositional_subsumption,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_3062,c_39,c_54,c_58]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_7377,plain,
% 51.73/7.00      ( r1_ordinal1(X0,X1) = iProver_top
% 51.73/7.00      | r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | v3_ordinal1(X1) != iProver_top ),
% 51.73/7.00      inference(renaming,[status(thm)],[c_7376]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47683,plain,
% 51.73/7.00      ( r1_ordinal1(sK2(sK4,sK4),sK4) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_47676,c_7377]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47687,plain,
% 51.73/7.00      ( v3_ordinal1(sK2(sK4,sK4)) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_47676,c_2016]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_47744,plain,
% 51.73/7.00      ( v4_ordinal1(sK4) = iProver_top ),
% 51.73/7.00      inference(global_propositional_subsumption,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_47656,c_29,c_76,c_2639,c_3253,c_3958,c_5319,c_9094,
% 51.73/7.00                 c_39107,c_47683,c_47687]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_44856,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK4,k3_tarski(X0))
% 51.73/7.00      | r1_tarski(sK4,k3_tarski(X0))
% 51.73/7.00      | ~ v3_ordinal1(k3_tarski(X0))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_44868,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK4,k3_tarski(sK4))
% 51.73/7.00      | r1_tarski(sK4,k3_tarski(sK4))
% 51.73/7.00      | ~ v3_ordinal1(k3_tarski(sK4))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_44856]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1417,plain,( X0 = X0 ),theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_42319,plain,
% 51.73/7.00      ( k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) = k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8,plain,
% 51.73/7.00      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 51.73/7.00      inference(cnf_transformation,[],[f92]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38258,plain,
% 51.73/7.00      ( r2_hidden(sK5,sK3(X0,sK5)) | ~ r2_hidden(sK5,k3_tarski(X0)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_8]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38274,plain,
% 51.73/7.00      ( r2_hidden(sK5,sK3(sK4,sK5)) | ~ r2_hidden(sK5,k3_tarski(sK4)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_38258]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_7,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f91]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38259,plain,
% 51.73/7.00      ( r2_hidden(sK3(X0,sK5),X0) | ~ r2_hidden(sK5,k3_tarski(X0)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_7]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38270,plain,
% 51.73/7.00      ( r2_hidden(sK3(sK4,sK5),sK4) | ~ r2_hidden(sK5,k3_tarski(sK4)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_38259]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_17127,plain,
% 51.73/7.00      ( r2_hidden(sK5,X0) | ~ r2_hidden(sK5,sK4) | ~ r1_tarski(sK4,X0) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38256,plain,
% 51.73/7.00      ( r2_hidden(sK5,k3_tarski(X0))
% 51.73/7.00      | ~ r2_hidden(sK5,sK4)
% 51.73/7.00      | ~ r1_tarski(sK4,k3_tarski(X0)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_17127]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_38262,plain,
% 51.73/7.00      ( r2_hidden(sK5,k3_tarski(sK4))
% 51.73/7.00      | ~ r2_hidden(sK5,sK4)
% 51.73/7.00      | ~ r1_tarski(sK4,k3_tarski(sK4)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_38256]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3048,plain,
% 51.73/7.00      ( r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(X2,k2_xboole_0(X2,k1_tarski(X2)))
% 51.73/7.00      | X0 != X2
% 51.73/7.00      | X1 != k2_xboole_0(X2,k1_tarski(X2)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1419]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_15200,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 51.73/7.00      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0)))
% 51.73/7.00      | X1 != X0
% 51.73/7.00      | k2_xboole_0(X0,k1_tarski(X0)) != k2_xboole_0(X0,k1_tarski(X0)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3048]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_28546,plain,
% 51.73/7.00      ( ~ r2_hidden(k3_tarski(sK4),k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
% 51.73/7.00      | r2_hidden(sK4,k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
% 51.73/7.00      | k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))) != k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4)))
% 51.73/7.00      | sK4 != k3_tarski(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_15200]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3035,plain,
% 51.73/7.00      ( r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | X1 != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))
% 51.73/7.00      | X0 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1419]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_28006,plain,
% 51.73/7.00      ( r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | X0 != k2_xboole_0(sK5,k1_tarski(sK5))
% 51.73/7.00      | k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3035]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_28008,plain,
% 51.73/7.00      ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r2_hidden(sK4,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) != k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))
% 51.73/7.00      | sK4 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_28006]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_18993,plain,
% 51.73/7.00      ( r1_ordinal1(sK4,k3_tarski(sK4))
% 51.73/7.00      | ~ r2_hidden(sK4,k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4))))
% 51.73/7.00      | ~ v3_ordinal1(k3_tarski(sK4))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_20,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 51.73/7.00      | ~ r2_hidden(X0,X1)
% 51.73/7.00      | ~ v3_ordinal1(X1)
% 51.73/7.00      | ~ v3_ordinal1(X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f85]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_169,plain,
% 51.73/7.00      ( ~ v3_ordinal1(X1)
% 51.73/7.00      | ~ r2_hidden(X0,X1)
% 51.73/7.00      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 51.73/7.00      inference(global_propositional_subsumption,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_20,c_17]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_170,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 51.73/7.00      | ~ r2_hidden(X0,X1)
% 51.73/7.00      | ~ v3_ordinal1(X1) ),
% 51.73/7.00      inference(renaming,[status(thm)],[c_169]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2365,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 51.73/7.00      | ~ r2_hidden(X0,sK4)
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_170]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_17156,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | ~ r2_hidden(sK5,sK4)
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2365]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_17163,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) = iProver_top
% 51.73/7.00      | r2_hidden(sK5,sK4) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_17156]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4880,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_170]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8440,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_4880]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8442,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r2_hidden(sK4,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_8440]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8267,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(X0,sK5),X1)
% 51.73/7.00      | r2_hidden(sK3(X0,sK5),k2_xboole_0(X1,k1_tarski(X1))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_15]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8269,plain,
% 51.73/7.00      ( r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK4,k1_tarski(sK4)))
% 51.73/7.00      | ~ r2_hidden(sK3(sK4,sK5),sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_8267]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2281,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r1_tarski(X1,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4300,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2281]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8237,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(X0,sK5),k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | r2_hidden(sK3(X0,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_4300]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8258,plain,
% 51.73/7.00      ( r2_hidden(sK3(sK4,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK4,k1_tarski(sK4)))
% 51.73/7.00      | ~ r1_tarski(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_8237]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_16,plain,
% 51.73/7.00      ( r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | X1 = X0 ),
% 51.73/7.00      inference(cnf_transformation,[],[f82]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2132,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8223,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(X0,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r2_hidden(sK3(X0,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK3(X0,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2132]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_8229,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(sK4,sK5),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r2_hidden(sK3(sK4,sK5),k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK3(sK4,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_8223]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_7082,plain,
% 51.73/7.00      ( r2_hidden(k3_tarski(sK4),k2_xboole_0(k3_tarski(sK4),k1_tarski(k3_tarski(sK4)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2974,plain,
% 51.73/7.00      ( ~ r1_ordinal1(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(X0)
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4958,plain,
% 51.73/7.00      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2974]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4967,plain,
% 51.73/7.00      ( ~ r1_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | r1_tarski(k2_xboole_0(sK4,k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_4958]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4569,plain,
% 51.73/7.00      ( k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) = k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4209,plain,
% 51.73/7.00      ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3141,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(X0,sK5),X1)
% 51.73/7.00      | ~ v3_ordinal1(X1)
% 51.73/7.00      | v3_ordinal1(sK3(X0,sK5)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_17]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3143,plain,
% 51.73/7.00      ( ~ r2_hidden(sK3(sK4,sK5),sK4)
% 51.73/7.00      | v3_ordinal1(sK3(sK4,sK5))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3141]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_21,plain,
% 51.73/7.00      ( ~ r1_ordinal1(X0,X1)
% 51.73/7.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 51.73/7.00      | ~ v3_ordinal1(X1)
% 51.73/7.00      | ~ v3_ordinal1(X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f86]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2961,plain,
% 51.73/7.00      ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0)))
% 51.73/7.00      | ~ v3_ordinal1(X0)
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_21]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2967,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0) != iProver_top
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 51.73/7.00      | v3_ordinal1(X0) != iProver_top
% 51.73/7.00      | v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2961]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2969,plain,
% 51.73/7.00      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) != iProver_top
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(sK4,k1_tarski(sK4))) = iProver_top
% 51.73/7.00      | v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
% 51.73/7.00      | v3_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2967]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2917,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
% 51.73/7.00      | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0)))
% 51.73/7.00      | X0 = k2_xboole_0(sK5,k1_tarski(sK5)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2918,plain,
% 51.73/7.00      ( X0 = k2_xboole_0(sK5,k1_tarski(sK5))
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0) = iProver_top
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2917]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2920,plain,
% 51.73/7.00      ( sK4 = k2_xboole_0(sK5,k1_tarski(sK5))
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
% 51.73/7.00      | r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) = iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2918]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1418,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2792,plain,
% 51.73/7.00      ( k3_tarski(X0) != X1 | sK4 != X1 | sK4 = k3_tarski(X0) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1418]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2793,plain,
% 51.73/7.00      ( k3_tarski(sK4) != sK4 | sK4 = k3_tarski(sK4) | sK4 != sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2792]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1422,plain,
% 51.73/7.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(X1) | X1 != X0 ),
% 51.73/7.00      theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2559,plain,
% 51.73/7.00      ( ~ v3_ordinal1(X0)
% 51.73/7.00      | v3_ordinal1(k3_tarski(X1))
% 51.73/7.00      | k3_tarski(X1) != X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1422]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2561,plain,
% 51.73/7.00      ( v3_ordinal1(k3_tarski(sK4))
% 51.73/7.00      | ~ v3_ordinal1(sK4)
% 51.73/7.00      | k3_tarski(sK4) != sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2559]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_18,plain,
% 51.73/7.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 51.73/7.00      inference(cnf_transformation,[],[f83]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2508,plain,
% 51.73/7.00      ( v3_ordinal1(k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5)))))
% 51.73/7.00      | ~ v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_18]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2487,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),k2_xboole_0(k2_xboole_0(sK5,k1_tarski(sK5)),k1_tarski(k2_xboole_0(sK5,k1_tarski(sK5))))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2090,plain,
% 51.73/7.00      ( v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)))
% 51.73/7.00      | ~ v3_ordinal1(sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_18]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2091,plain,
% 51.73/7.00      ( v3_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
% 51.73/7.00      | v3_ordinal1(sK5) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_233,plain,
% 51.73/7.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 51.73/7.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_24,negated_conjecture,
% 51.73/7.00      ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | ~ v4_ordinal1(sK4) ),
% 51.73/7.00      inference(cnf_transformation,[],[f88]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_449,plain,
% 51.73/7.00      ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | k3_tarski(X0) != X0
% 51.73/7.00      | sK4 != X0 ),
% 51.73/7.00      inference(resolution_lifted,[status(thm)],[c_233,c_24]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_450,plain,
% 51.73/7.00      ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 51.73/7.00      | k3_tarski(sK4) != sK4 ),
% 51.73/7.00      inference(unflattening,[status(thm)],[c_449]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_25,negated_conjecture,
% 51.73/7.00      ( r2_hidden(sK5,sK4) | ~ v4_ordinal1(sK4) ),
% 51.73/7.00      inference(cnf_transformation,[],[f77]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_439,plain,
% 51.73/7.00      ( r2_hidden(sK5,sK4) | k3_tarski(X0) != X0 | sK4 != X0 ),
% 51.73/7.00      inference(resolution_lifted,[status(thm)],[c_233,c_25]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_440,plain,
% 51.73/7.00      ( r2_hidden(sK5,sK4) | k3_tarski(sK4) != sK4 ),
% 51.73/7.00      inference(unflattening,[status(thm)],[c_439]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_26,negated_conjecture,
% 51.73/7.00      ( v3_ordinal1(sK5) | ~ v4_ordinal1(sK4) ),
% 51.73/7.00      inference(cnf_transformation,[],[f76]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_429,plain,
% 51.73/7.00      ( v3_ordinal1(sK5) | k3_tarski(X0) != X0 | sK4 != X0 ),
% 51.73/7.00      inference(resolution_lifted,[status(thm)],[c_233,c_26]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_430,plain,
% 51.73/7.00      ( v3_ordinal1(sK5) | k3_tarski(sK4) != sK4 ),
% 51.73/7.00      inference(unflattening,[status(thm)],[c_429]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_10,plain,
% 51.73/7.00      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 51.73/7.00      inference(cnf_transformation,[],[f59]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_71,plain,
% 51.73/7.00      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_73,plain,
% 51.73/7.00      ( k3_tarski(sK4) = sK4 | v4_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_71]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_66,plain,
% 51.73/7.00      ( ~ r1_ordinal1(sK4,sK4)
% 51.73/7.00      | r1_tarski(sK4,sK4)
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_14,plain,
% 51.73/7.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 51.73/7.00      inference(cnf_transformation,[],[f93]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_62,plain,
% 51.73/7.00      ( r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_14]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_56,plain,
% 51.73/7.00      ( ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
% 51.73/7.00      | r2_hidden(sK4,sK4)
% 51.73/7.00      | sK4 = sK4 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_52,plain,
% 51.73/7.00      ( v3_ordinal1(k2_xboole_0(sK4,k1_tarski(sK4)))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_18]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_40,plain,
% 51.73/7.00      ( r1_ordinal1(sK4,sK4)
% 51.73/7.00      | ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
% 51.73/7.00      | ~ v3_ordinal1(sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_37,plain,
% 51.73/7.00      ( ~ r2_hidden(sK4,sK4) | ~ r1_tarski(sK4,sK4) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_35,plain,
% 51.73/7.00      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4) != iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_34,plain,
% 51.73/7.00      ( r2_hidden(sK5,sK4) = iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_33,plain,
% 51.73/7.00      ( v3_ordinal1(sK5) = iProver_top
% 51.73/7.00      | v4_ordinal1(sK4) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(contradiction,plain,
% 51.73/7.00      ( $false ),
% 51.73/7.00      inference(minisat,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_151992,c_109027,c_108965,c_104524,c_102089,c_93885,
% 51.73/7.00                 c_91937,c_47744,c_44868,c_42319,c_38274,c_38270,c_38262,
% 51.73/7.00                 c_28546,c_28008,c_18993,c_17163,c_8442,c_8269,c_8258,
% 51.73/7.00                 c_8229,c_7082,c_4967,c_4569,c_4209,c_3143,c_2969,c_2920,
% 51.73/7.00                 c_2793,c_2561,c_2508,c_2487,c_2091,c_2090,c_450,c_440,
% 51.73/7.00                 c_430,c_73,c_66,c_62,c_56,c_52,c_40,c_37,c_35,c_34,c_33,
% 51.73/7.00                 c_29,c_28]) ).
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  ------                               Statistics
% 51.73/7.00  
% 51.73/7.00  ------ General
% 51.73/7.00  
% 51.73/7.00  abstr_ref_over_cycles:                  0
% 51.73/7.00  abstr_ref_under_cycles:                 0
% 51.73/7.00  gc_basic_clause_elim:                   0
% 51.73/7.00  forced_gc_time:                         0
% 51.73/7.00  parsing_time:                           0.01
% 51.73/7.00  unif_index_cands_time:                  0.
% 51.73/7.00  unif_index_add_time:                    0.
% 51.73/7.00  orderings_time:                         0.
% 51.73/7.00  out_proof_time:                         0.025
% 51.73/7.00  total_time:                             6.163
% 51.73/7.00  num_of_symbols:                         45
% 51.73/7.00  num_of_terms:                           149503
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing
% 51.73/7.00  
% 51.73/7.00  num_of_splits:                          0
% 51.73/7.00  num_of_split_atoms:                     0
% 51.73/7.00  num_of_reused_defs:                     0
% 51.73/7.00  num_eq_ax_congr_red:                    36
% 51.73/7.00  num_of_sem_filtered_clauses:            1
% 51.73/7.00  num_of_subtypes:                        0
% 51.73/7.00  monotx_restored_types:                  0
% 51.73/7.00  sat_num_of_epr_types:                   0
% 51.73/7.00  sat_num_of_non_cyclic_types:            0
% 51.73/7.00  sat_guarded_non_collapsed_types:        0
% 51.73/7.00  num_pure_diseq_elim:                    0
% 51.73/7.00  simp_replaced_by:                       0
% 51.73/7.00  res_preprocessed:                       129
% 51.73/7.00  prep_upred:                             0
% 51.73/7.00  prep_unflattend:                        48
% 51.73/7.00  smt_new_axioms:                         0
% 51.73/7.00  pred_elim_cands:                        5
% 51.73/7.00  pred_elim:                              0
% 51.73/7.00  pred_elim_cl:                           0
% 51.73/7.00  pred_elim_cycles:                       6
% 51.73/7.00  merged_defs:                            8
% 51.73/7.00  merged_defs_ncl:                        0
% 51.73/7.00  bin_hyper_res:                          8
% 51.73/7.00  prep_cycles:                            4
% 51.73/7.00  pred_elim_time:                         0.007
% 51.73/7.00  splitting_time:                         0.
% 51.73/7.00  sem_filter_time:                        0.
% 51.73/7.00  monotx_time:                            0.
% 51.73/7.00  subtype_inf_time:                       0.
% 51.73/7.00  
% 51.73/7.00  ------ Problem properties
% 51.73/7.00  
% 51.73/7.00  clauses:                                28
% 51.73/7.00  conjectures:                            5
% 51.73/7.00  epr:                                    8
% 51.73/7.00  horn:                                   23
% 51.73/7.00  ground:                                 4
% 51.73/7.00  unary:                                  2
% 51.73/7.00  binary:                                 12
% 51.73/7.00  lits:                                   75
% 51.73/7.00  lits_eq:                                6
% 51.73/7.00  fd_pure:                                0
% 51.73/7.00  fd_pseudo:                              0
% 51.73/7.00  fd_cond:                                0
% 51.73/7.00  fd_pseudo_cond:                         4
% 51.73/7.00  ac_symbols:                             0
% 51.73/7.00  
% 51.73/7.00  ------ Propositional Solver
% 51.73/7.00  
% 51.73/7.00  prop_solver_calls:                      74
% 51.73/7.00  prop_fast_solver_calls:                 10886
% 51.73/7.00  smt_solver_calls:                       0
% 51.73/7.00  smt_fast_solver_calls:                  0
% 51.73/7.00  prop_num_of_clauses:                    73178
% 51.73/7.00  prop_preprocess_simplified:             115641
% 51.73/7.00  prop_fo_subsumed:                       4253
% 51.73/7.00  prop_solver_time:                       0.
% 51.73/7.00  smt_solver_time:                        0.
% 51.73/7.00  smt_fast_solver_time:                   0.
% 51.73/7.00  prop_fast_solver_time:                  0.
% 51.73/7.00  prop_unsat_core_time:                   0.006
% 51.73/7.00  
% 51.73/7.00  ------ QBF
% 51.73/7.00  
% 51.73/7.00  qbf_q_res:                              0
% 51.73/7.00  qbf_num_tautologies:                    0
% 51.73/7.00  qbf_prep_cycles:                        0
% 51.73/7.00  
% 51.73/7.00  ------ BMC1
% 51.73/7.00  
% 51.73/7.00  bmc1_current_bound:                     -1
% 51.73/7.00  bmc1_last_solved_bound:                 -1
% 51.73/7.00  bmc1_unsat_core_size:                   -1
% 51.73/7.00  bmc1_unsat_core_parents_size:           -1
% 51.73/7.00  bmc1_merge_next_fun:                    0
% 51.73/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation
% 51.73/7.00  
% 51.73/7.00  inst_num_of_clauses:                    4523
% 51.73/7.00  inst_num_in_passive:                    910
% 51.73/7.00  inst_num_in_active:                     3687
% 51.73/7.00  inst_num_in_unprocessed:                2143
% 51.73/7.00  inst_num_of_loops:                      4819
% 51.73/7.00  inst_num_of_learning_restarts:          1
% 51.73/7.00  inst_num_moves_active_passive:          1128
% 51.73/7.00  inst_lit_activity:                      0
% 51.73/7.00  inst_lit_activity_moves:                0
% 51.73/7.00  inst_num_tautologies:                   0
% 51.73/7.00  inst_num_prop_implied:                  0
% 51.73/7.00  inst_num_existing_simplified:           0
% 51.73/7.00  inst_num_eq_res_simplified:             0
% 51.73/7.00  inst_num_child_elim:                    0
% 51.73/7.00  inst_num_of_dismatching_blockings:      22001
% 51.73/7.00  inst_num_of_non_proper_insts:           13485
% 51.73/7.00  inst_num_of_duplicates:                 0
% 51.73/7.00  inst_inst_num_from_inst_to_res:         0
% 51.73/7.00  inst_dismatching_checking_time:         0.
% 51.73/7.00  
% 51.73/7.00  ------ Resolution
% 51.73/7.00  
% 51.73/7.00  res_num_of_clauses:                     36
% 51.73/7.00  res_num_in_passive:                     36
% 51.73/7.00  res_num_in_active:                      0
% 51.73/7.00  res_num_of_loops:                       133
% 51.73/7.00  res_forward_subset_subsumed:            516
% 51.73/7.00  res_backward_subset_subsumed:           18
% 51.73/7.00  res_forward_subsumed:                   0
% 51.73/7.00  res_backward_subsumed:                  0
% 51.73/7.00  res_forward_subsumption_resolution:     1
% 51.73/7.00  res_backward_subsumption_resolution:    0
% 51.73/7.00  res_clause_to_clause_subsumption:       156993
% 51.73/7.00  res_orphan_elimination:                 0
% 51.73/7.00  res_tautology_del:                      1026
% 51.73/7.00  res_num_eq_res_simplified:              0
% 51.73/7.00  res_num_sel_changes:                    0
% 51.73/7.00  res_moves_from_active_to_pass:          0
% 51.73/7.00  
% 51.73/7.00  ------ Superposition
% 51.73/7.00  
% 51.73/7.00  sup_time_total:                         0.
% 51.73/7.00  sup_time_generating:                    0.
% 51.73/7.00  sup_time_sim_full:                      0.
% 51.73/7.00  sup_time_sim_immed:                     0.
% 51.73/7.00  
% 51.73/7.00  sup_num_of_clauses:                     13968
% 51.73/7.00  sup_num_in_active:                      713
% 51.73/7.00  sup_num_in_passive:                     13255
% 51.73/7.00  sup_num_of_loops:                       962
% 51.73/7.00  sup_fw_superposition:                   9362
% 51.73/7.00  sup_bw_superposition:                   10035
% 51.73/7.00  sup_immediate_simplified:               2227
% 51.73/7.00  sup_given_eliminated:                   3
% 51.73/7.00  comparisons_done:                       0
% 51.73/7.00  comparisons_avoided:                    65
% 51.73/7.00  
% 51.73/7.00  ------ Simplifications
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  sim_fw_subset_subsumed:                 1195
% 51.73/7.00  sim_bw_subset_subsumed:                 477
% 51.73/7.00  sim_fw_subsumed:                        791
% 51.73/7.00  sim_bw_subsumed:                        212
% 51.73/7.00  sim_fw_subsumption_res:                 0
% 51.73/7.00  sim_bw_subsumption_res:                 0
% 51.73/7.00  sim_tautology_del:                      640
% 51.73/7.00  sim_eq_tautology_del:                   115
% 51.73/7.00  sim_eq_res_simp:                        9
% 51.73/7.00  sim_fw_demodulated:                     42
% 51.73/7.00  sim_bw_demodulated:                     52
% 51.73/7.00  sim_light_normalised:                   196
% 51.73/7.00  sim_joinable_taut:                      0
% 51.73/7.00  sim_joinable_simp:                      0
% 51.73/7.00  sim_ac_normalised:                      0
% 51.73/7.00  sim_smt_subsumption:                    0
% 51.73/7.00  
%------------------------------------------------------------------------------
