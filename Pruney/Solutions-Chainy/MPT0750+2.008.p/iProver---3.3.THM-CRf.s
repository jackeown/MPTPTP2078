%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:01 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :  275 (4825 expanded)
%              Number of clauses        :  177 (1511 expanded)
%              Number of leaves         :   24 (1062 expanded)
%              Depth                    :   28
%              Number of atoms          :  908 (22160 expanded)
%              Number of equality atoms :  389 (3907 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f51])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f106,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f83,f77])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f85,f77])).

fof(f118,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f104])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
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
            ( ~ r2_hidden(k1_ordinal1(X1),sK6)
            & r2_hidden(X1,sK6)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK6) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK6)
            | ~ r2_hidden(X2,sK6)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK6) )
      & v3_ordinal1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
        & r2_hidden(sK7,sK6)
        & v3_ordinal1(sK7) )
      | ~ v4_ordinal1(sK6) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK6)
          | ~ r2_hidden(X2,sK6)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK6) )
    & v3_ordinal1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f62,f61])).

fof(f99,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f112,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f99,f77])).

fof(f72,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f72])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f77])).

fof(f15,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f54])).

fof(f92,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f89,f77])).

fof(f102,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f111,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f102,f77])).

fof(f100,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f90,f77])).

fof(f78,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1719,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1707,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4561,plain,
    ( sK2(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
    | r2_hidden(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_1707])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1709,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1692,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1717,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4533,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1692,c_1717])).

cnf(c_5023,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_4533])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1696,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6392,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k3_tarski(sK6),X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5023,c_1696])).

cnf(c_37,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_38,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_13,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_96,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_98,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1919,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1926,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2392,plain,
    ( ~ r1_ordinal1(sK3(X0,X1),sK6)
    | r1_tarski(sK3(X0,X1),sK6)
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2403,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
    | r1_tarski(sK3(X0,X1),sK6) = iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_2405,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_2646,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6)
    | ~ r2_hidden(k3_tarski(sK6),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2647,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) = iProver_top
    | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1715,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2972,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1715,c_1696])).

cnf(c_2974,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2972])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1716,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3124,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(X1,sK3(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1696])).

cnf(c_3126,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3124])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1706,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3837,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1706])).

cnf(c_3846,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3837])).

cnf(c_5452,plain,
    ( ~ r1_ordinal1(X0,sK3(sK6,X1))
    | r1_tarski(X0,sK3(sK6,X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5463,plain,
    ( r1_ordinal1(X0,sK3(sK6,X1)) != iProver_top
    | r1_tarski(X0,sK3(sK6,X1)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(sK6,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5452])).

cnf(c_5465,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK6)) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5463])).

cnf(c_12,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5587,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6)
    | r1_ordinal1(sK6,sK3(X0,X1))
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5588,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6) = iProver_top
    | r1_ordinal1(sK6,sK3(X0,X1)) = iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5587])).

cnf(c_5590,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
    | r1_ordinal1(sK6,sK3(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5588])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1721,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1708,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2826,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1696])).

cnf(c_3496,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_2826])).

cnf(c_6396,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5023,c_3496])).

cnf(c_28,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1700,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3841,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4(X0)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1706])).

cnf(c_27,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_60,plain,
    ( v3_ordinal1(sK4(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8682,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3841,c_60])).

cnf(c_8685,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8682])).

cnf(c_24,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_10566,plain,
    ( v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))))
    | ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_10567,plain,
    ( v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10566])).

cnf(c_10943,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6392,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567])).

cnf(c_1705,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1695,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5531,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1695])).

cnf(c_35,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_42,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_43,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK6,sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_45,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_47,plain,
    ( r2_hidden(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_26,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_64,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_63,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_65,plain,
    ( r1_ordinal1(sK6,sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_73,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_84,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_83,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_85,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_88,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_tarski(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_87,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_89,plain,
    ( r1_ordinal1(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_1819,plain,
    ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1830,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = X0
    | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

cnf(c_1832,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1830])).

cnf(c_994,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1871,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2114,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(sK7,sK6)
    | X0 != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2116,plain,
    ( X0 != sK7
    | sK6 != sK6
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_2118,plain,
    ( sK6 != sK6
    | sK6 != sK7
    | r2_hidden(sK6,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2271,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2272,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_993,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2616,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_2617,plain,
    ( sK6 != sK6
    | sK6 = sK7
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_3528,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(X0,sK7)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3534,plain,
    ( sK7 = X0
    | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3528])).

cnf(c_3536,plain,
    ( sK7 = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3534])).

cnf(c_1694,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4532,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_1717])).

cnf(c_4545,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | r2_hidden(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4532])).

cnf(c_6142,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5531,c_37,c_38,c_42,c_43,c_44,c_46,c_47,c_64,c_65,c_73,c_84,c_85,c_88,c_89,c_1832,c_2118,c_2272,c_2405,c_2617,c_2974,c_3126,c_3536,c_3846,c_4545,c_5465,c_5590])).

cnf(c_10948,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_10943,c_6142])).

cnf(c_11091,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10948,c_1708])).

cnf(c_45299,plain,
    ( sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = sK7
    | k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
    | r2_hidden(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4561,c_11091])).

cnf(c_14,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1712,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10947,plain,
    ( k3_tarski(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_10943,c_1712])).

cnf(c_45315,plain,
    ( sK2(sK6,X0) = sK7
    | sK6 = X0
    | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45299,c_10947,c_10948])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1724,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1725,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2825,plain,
    ( r2_hidden(sK0(X0,k2_xboole_0(X1,k1_tarski(X1))),X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1725])).

cnf(c_6527,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_2825])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1723,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4996,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(k3_tarski(sK6),X1) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4532,c_1723])).

cnf(c_6779,plain,
    ( r2_hidden(X0,k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6527,c_4996])).

cnf(c_1702,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9782,plain,
    ( r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6779,c_1702])).

cnf(c_3840,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1706])).

cnf(c_16203,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10948,c_3840])).

cnf(c_4997,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4532,c_1706])).

cnf(c_16983,plain,
    ( v3_ordinal1(X0) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16203,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,c_3846,c_4997,c_5465,c_5590,c_6396,c_8685,c_10567])).

cnf(c_16984,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_16983])).

cnf(c_34814,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9782,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567,c_16984])).

cnf(c_34815,plain,
    ( r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_34814])).

cnf(c_34818,plain,
    ( r1_ordinal1(X0,sK6) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34815,c_10947])).

cnf(c_45941,plain,
    ( sK2(sK6,sK7) = sK7
    | sK6 = sK7
    | r1_ordinal1(sK1(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_45315,c_34818])).

cnf(c_93,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_95,plain,
    ( k3_tarski(sK6) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_290,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_525,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_34])).

cnf(c_526,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_2428,plain,
    ( k3_tarski(X0) != X1
    | sK6 != X1
    | sK6 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_2429,plain,
    ( k3_tarski(sK6) != sK6
    | sK6 = k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(c_2608,plain,
    ( r2_hidden(k3_tarski(X0),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(X0) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_2610,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_2638,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_tarski(sK6),sK6)
    | X0 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2641,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,sK6)
    | sK6 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_27726,plain,
    ( r2_hidden(sK2(X0,sK7),X0)
    | r2_hidden(sK1(X0,sK7),sK7)
    | k3_tarski(X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_27728,plain,
    ( k3_tarski(X0) = sK7
    | r2_hidden(sK2(X0,sK7),X0) = iProver_top
    | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27726])).

cnf(c_27730,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_27728])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19524,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ r2_hidden(sK1(sK6,X0),sK7)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_52180,plain,
    ( ~ r2_hidden(sK1(sK6,sK7),sK7)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_19524])).

cnf(c_52189,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK1(sK6,sK7),sK7) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52180])).

cnf(c_58177,plain,
    ( r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45941,c_37,c_38,c_43,c_46,c_64,c_73,c_84,c_88,c_95,c_98,c_526,c_1926,c_2405,c_2429,c_2610,c_2641,c_2647,c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567,c_27730,c_52189])).

cnf(c_11089,plain,
    ( r1_ordinal1(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10948,c_1702])).

cnf(c_13207,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_ordinal1(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11089,c_38,c_42,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567])).

cnf(c_13208,plain,
    ( r1_ordinal1(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13207])).

cnf(c_58189,plain,
    ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top
    | v3_ordinal1(sK2(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_58177,c_13208])).

cnf(c_10689,plain,
    ( ~ r2_hidden(sK2(X0,X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_51135,plain,
    ( ~ r2_hidden(sK2(sK6,sK7),sK6)
    | v3_ordinal1(sK2(sK6,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_10689])).

cnf(c_51137,plain,
    ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
    | v3_ordinal1(sK2(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51135])).

cnf(c_58205,plain,
    ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58189,c_37,c_38,c_43,c_46,c_64,c_73,c_84,c_88,c_95,c_98,c_526,c_1926,c_2405,c_2429,c_2610,c_2641,c_2647,c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567,c_27730,c_51137,c_52189])).

cnf(c_1710,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_58210,plain,
    ( r1_tarski(sK2(sK6,sK7),sK7) = iProver_top
    | v3_ordinal1(sK2(sK6,sK7)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_58205,c_1710])).

cnf(c_4308,plain,
    ( r2_hidden(sK1(X0,X1),X2)
    | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | ~ r1_tarski(sK2(X0,X1),X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19911,plain,
    ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | r2_hidden(sK1(X0,X1),sK7)
    | ~ r1_tarski(sK2(X0,X1),sK7) ),
    inference(instantiation,[status(thm)],[c_4308])).

cnf(c_54459,plain,
    ( ~ r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
    | r2_hidden(sK1(X0,sK7),sK7)
    | ~ r1_tarski(sK2(X0,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_19911])).

cnf(c_54460,plain,
    ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) != iProver_top
    | r2_hidden(sK1(X0,sK7),sK7) = iProver_top
    | r1_tarski(sK2(X0,sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54459])).

cnf(c_54462,plain,
    ( r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) != iProver_top
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top
    | r1_tarski(sK2(sK6,sK7),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54460])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7155,plain,
    ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
    | r2_hidden(sK1(X0,sK7),sK7)
    | k3_tarski(X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7157,plain,
    ( k3_tarski(X0) = sK7
    | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) = iProver_top
    | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7155])).

cnf(c_7159,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) = iProver_top
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7157])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58210,c_54462,c_52189,c_51137,c_27730,c_10943,c_7159,c_2641,c_2610,c_2429,c_526,c_95,c_88,c_84,c_73,c_64,c_46,c_43,c_42,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.37/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.37/2.49  
% 15.37/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.37/2.49  
% 15.37/2.49  ------  iProver source info
% 15.37/2.49  
% 15.37/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.37/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.37/2.49  git: non_committed_changes: false
% 15.37/2.49  git: last_make_outside_of_git: false
% 15.37/2.49  
% 15.37/2.49  ------ 
% 15.37/2.49  
% 15.37/2.49  ------ Input Options
% 15.37/2.49  
% 15.37/2.49  --out_options                           all
% 15.37/2.49  --tptp_safe_out                         true
% 15.37/2.49  --problem_path                          ""
% 15.37/2.49  --include_path                          ""
% 15.37/2.49  --clausifier                            res/vclausify_rel
% 15.37/2.49  --clausifier_options                    ""
% 15.37/2.49  --stdin                                 false
% 15.37/2.49  --stats_out                             all
% 15.37/2.49  
% 15.37/2.49  ------ General Options
% 15.37/2.49  
% 15.37/2.49  --fof                                   false
% 15.37/2.49  --time_out_real                         305.
% 15.37/2.49  --time_out_virtual                      -1.
% 15.37/2.49  --symbol_type_check                     false
% 15.37/2.49  --clausify_out                          false
% 15.37/2.49  --sig_cnt_out                           false
% 15.37/2.49  --trig_cnt_out                          false
% 15.37/2.49  --trig_cnt_out_tolerance                1.
% 15.37/2.49  --trig_cnt_out_sk_spl                   false
% 15.37/2.49  --abstr_cl_out                          false
% 15.37/2.49  
% 15.37/2.49  ------ Global Options
% 15.37/2.49  
% 15.37/2.49  --schedule                              default
% 15.37/2.49  --add_important_lit                     false
% 15.37/2.49  --prop_solver_per_cl                    1000
% 15.37/2.49  --min_unsat_core                        false
% 15.37/2.49  --soft_assumptions                      false
% 15.37/2.49  --soft_lemma_size                       3
% 15.37/2.49  --prop_impl_unit_size                   0
% 15.37/2.49  --prop_impl_unit                        []
% 15.37/2.49  --share_sel_clauses                     true
% 15.37/2.49  --reset_solvers                         false
% 15.37/2.49  --bc_imp_inh                            [conj_cone]
% 15.37/2.49  --conj_cone_tolerance                   3.
% 15.37/2.49  --extra_neg_conj                        none
% 15.37/2.49  --large_theory_mode                     true
% 15.37/2.49  --prolific_symb_bound                   200
% 15.37/2.49  --lt_threshold                          2000
% 15.37/2.49  --clause_weak_htbl                      true
% 15.37/2.49  --gc_record_bc_elim                     false
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing Options
% 15.37/2.49  
% 15.37/2.49  --preprocessing_flag                    true
% 15.37/2.49  --time_out_prep_mult                    0.1
% 15.37/2.49  --splitting_mode                        input
% 15.37/2.49  --splitting_grd                         true
% 15.37/2.49  --splitting_cvd                         false
% 15.37/2.49  --splitting_cvd_svl                     false
% 15.37/2.49  --splitting_nvd                         32
% 15.37/2.49  --sub_typing                            true
% 15.37/2.49  --prep_gs_sim                           true
% 15.37/2.49  --prep_unflatten                        true
% 15.37/2.49  --prep_res_sim                          true
% 15.37/2.49  --prep_upred                            true
% 15.37/2.49  --prep_sem_filter                       exhaustive
% 15.37/2.49  --prep_sem_filter_out                   false
% 15.37/2.49  --pred_elim                             true
% 15.37/2.49  --res_sim_input                         true
% 15.37/2.49  --eq_ax_congr_red                       true
% 15.37/2.49  --pure_diseq_elim                       true
% 15.37/2.49  --brand_transform                       false
% 15.37/2.49  --non_eq_to_eq                          false
% 15.37/2.49  --prep_def_merge                        true
% 15.37/2.49  --prep_def_merge_prop_impl              false
% 15.37/2.49  --prep_def_merge_mbd                    true
% 15.37/2.49  --prep_def_merge_tr_red                 false
% 15.37/2.49  --prep_def_merge_tr_cl                  false
% 15.37/2.49  --smt_preprocessing                     true
% 15.37/2.49  --smt_ac_axioms                         fast
% 15.37/2.49  --preprocessed_out                      false
% 15.37/2.49  --preprocessed_stats                    false
% 15.37/2.49  
% 15.37/2.49  ------ Abstraction refinement Options
% 15.37/2.49  
% 15.37/2.49  --abstr_ref                             []
% 15.37/2.49  --abstr_ref_prep                        false
% 15.37/2.49  --abstr_ref_until_sat                   false
% 15.37/2.49  --abstr_ref_sig_restrict                funpre
% 15.37/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.37/2.49  --abstr_ref_under                       []
% 15.37/2.49  
% 15.37/2.49  ------ SAT Options
% 15.37/2.49  
% 15.37/2.49  --sat_mode                              false
% 15.37/2.49  --sat_fm_restart_options                ""
% 15.37/2.49  --sat_gr_def                            false
% 15.37/2.49  --sat_epr_types                         true
% 15.37/2.49  --sat_non_cyclic_types                  false
% 15.37/2.49  --sat_finite_models                     false
% 15.37/2.49  --sat_fm_lemmas                         false
% 15.37/2.49  --sat_fm_prep                           false
% 15.37/2.49  --sat_fm_uc_incr                        true
% 15.37/2.49  --sat_out_model                         small
% 15.37/2.49  --sat_out_clauses                       false
% 15.37/2.49  
% 15.37/2.49  ------ QBF Options
% 15.37/2.49  
% 15.37/2.49  --qbf_mode                              false
% 15.37/2.49  --qbf_elim_univ                         false
% 15.37/2.49  --qbf_dom_inst                          none
% 15.37/2.49  --qbf_dom_pre_inst                      false
% 15.37/2.49  --qbf_sk_in                             false
% 15.37/2.49  --qbf_pred_elim                         true
% 15.37/2.49  --qbf_split                             512
% 15.37/2.49  
% 15.37/2.49  ------ BMC1 Options
% 15.37/2.49  
% 15.37/2.49  --bmc1_incremental                      false
% 15.37/2.49  --bmc1_axioms                           reachable_all
% 15.37/2.49  --bmc1_min_bound                        0
% 15.37/2.49  --bmc1_max_bound                        -1
% 15.37/2.49  --bmc1_max_bound_default                -1
% 15.37/2.49  --bmc1_symbol_reachability              true
% 15.37/2.49  --bmc1_property_lemmas                  false
% 15.37/2.49  --bmc1_k_induction                      false
% 15.37/2.49  --bmc1_non_equiv_states                 false
% 15.37/2.49  --bmc1_deadlock                         false
% 15.37/2.49  --bmc1_ucm                              false
% 15.37/2.49  --bmc1_add_unsat_core                   none
% 15.37/2.49  --bmc1_unsat_core_children              false
% 15.37/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.37/2.49  --bmc1_out_stat                         full
% 15.37/2.49  --bmc1_ground_init                      false
% 15.37/2.49  --bmc1_pre_inst_next_state              false
% 15.37/2.49  --bmc1_pre_inst_state                   false
% 15.37/2.49  --bmc1_pre_inst_reach_state             false
% 15.37/2.49  --bmc1_out_unsat_core                   false
% 15.37/2.49  --bmc1_aig_witness_out                  false
% 15.37/2.49  --bmc1_verbose                          false
% 15.37/2.49  --bmc1_dump_clauses_tptp                false
% 15.37/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.37/2.49  --bmc1_dump_file                        -
% 15.37/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.37/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.37/2.49  --bmc1_ucm_extend_mode                  1
% 15.37/2.49  --bmc1_ucm_init_mode                    2
% 15.37/2.49  --bmc1_ucm_cone_mode                    none
% 15.37/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.37/2.49  --bmc1_ucm_relax_model                  4
% 15.37/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.37/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.37/2.49  --bmc1_ucm_layered_model                none
% 15.37/2.49  --bmc1_ucm_max_lemma_size               10
% 15.37/2.49  
% 15.37/2.49  ------ AIG Options
% 15.37/2.49  
% 15.37/2.49  --aig_mode                              false
% 15.37/2.49  
% 15.37/2.49  ------ Instantiation Options
% 15.37/2.49  
% 15.37/2.49  --instantiation_flag                    true
% 15.37/2.49  --inst_sos_flag                         true
% 15.37/2.49  --inst_sos_phase                        true
% 15.37/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.37/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.37/2.49  --inst_lit_sel_side                     num_symb
% 15.37/2.49  --inst_solver_per_active                1400
% 15.37/2.49  --inst_solver_calls_frac                1.
% 15.37/2.49  --inst_passive_queue_type               priority_queues
% 15.37/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.37/2.49  --inst_passive_queues_freq              [25;2]
% 15.37/2.49  --inst_dismatching                      true
% 15.37/2.49  --inst_eager_unprocessed_to_passive     true
% 15.37/2.49  --inst_prop_sim_given                   true
% 15.37/2.49  --inst_prop_sim_new                     false
% 15.37/2.49  --inst_subs_new                         false
% 15.37/2.49  --inst_eq_res_simp                      false
% 15.37/2.49  --inst_subs_given                       false
% 15.37/2.49  --inst_orphan_elimination               true
% 15.37/2.49  --inst_learning_loop_flag               true
% 15.37/2.49  --inst_learning_start                   3000
% 15.37/2.49  --inst_learning_factor                  2
% 15.37/2.49  --inst_start_prop_sim_after_learn       3
% 15.37/2.49  --inst_sel_renew                        solver
% 15.37/2.49  --inst_lit_activity_flag                true
% 15.37/2.49  --inst_restr_to_given                   false
% 15.37/2.49  --inst_activity_threshold               500
% 15.37/2.49  --inst_out_proof                        true
% 15.37/2.49  
% 15.37/2.49  ------ Resolution Options
% 15.37/2.49  
% 15.37/2.49  --resolution_flag                       true
% 15.37/2.49  --res_lit_sel                           adaptive
% 15.37/2.49  --res_lit_sel_side                      none
% 15.37/2.49  --res_ordering                          kbo
% 15.37/2.49  --res_to_prop_solver                    active
% 15.37/2.49  --res_prop_simpl_new                    false
% 15.37/2.49  --res_prop_simpl_given                  true
% 15.37/2.49  --res_passive_queue_type                priority_queues
% 15.37/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.37/2.49  --res_passive_queues_freq               [15;5]
% 15.37/2.49  --res_forward_subs                      full
% 15.37/2.49  --res_backward_subs                     full
% 15.37/2.49  --res_forward_subs_resolution           true
% 15.37/2.49  --res_backward_subs_resolution          true
% 15.37/2.49  --res_orphan_elimination                true
% 15.37/2.49  --res_time_limit                        2.
% 15.37/2.49  --res_out_proof                         true
% 15.37/2.49  
% 15.37/2.49  ------ Superposition Options
% 15.37/2.49  
% 15.37/2.49  --superposition_flag                    true
% 15.37/2.49  --sup_passive_queue_type                priority_queues
% 15.37/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.37/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.37/2.49  --demod_completeness_check              fast
% 15.37/2.49  --demod_use_ground                      true
% 15.37/2.49  --sup_to_prop_solver                    passive
% 15.37/2.49  --sup_prop_simpl_new                    true
% 15.37/2.49  --sup_prop_simpl_given                  true
% 15.37/2.49  --sup_fun_splitting                     true
% 15.37/2.49  --sup_smt_interval                      50000
% 15.37/2.49  
% 15.37/2.49  ------ Superposition Simplification Setup
% 15.37/2.49  
% 15.37/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.37/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.37/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.37/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.37/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.37/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.37/2.49  --sup_immed_triv                        [TrivRules]
% 15.37/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_immed_bw_main                     []
% 15.37/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.37/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.37/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_input_bw                          []
% 15.37/2.49  
% 15.37/2.49  ------ Combination Options
% 15.37/2.49  
% 15.37/2.49  --comb_res_mult                         3
% 15.37/2.49  --comb_sup_mult                         2
% 15.37/2.49  --comb_inst_mult                        10
% 15.37/2.49  
% 15.37/2.49  ------ Debug Options
% 15.37/2.49  
% 15.37/2.49  --dbg_backtrace                         false
% 15.37/2.49  --dbg_dump_prop_clauses                 false
% 15.37/2.49  --dbg_dump_prop_clauses_file            -
% 15.37/2.49  --dbg_out_stat                          false
% 15.37/2.49  ------ Parsing...
% 15.37/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.37/2.49  ------ Proving...
% 15.37/2.49  ------ Problem Properties 
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  clauses                                 36
% 15.37/2.49  conjectures                             5
% 15.37/2.49  EPR                                     12
% 15.37/2.49  Horn                                    27
% 15.37/2.49  unary                                   6
% 15.37/2.49  binary                                  14
% 15.37/2.49  lits                                    91
% 15.37/2.49  lits eq                                 9
% 15.37/2.49  fd_pure                                 0
% 15.37/2.49  fd_pseudo                               0
% 15.37/2.49  fd_cond                                 0
% 15.37/2.49  fd_pseudo_cond                          6
% 15.37/2.49  AC symbols                              0
% 15.37/2.49  
% 15.37/2.49  ------ Schedule dynamic 5 is on 
% 15.37/2.49  
% 15.37/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  ------ 
% 15.37/2.49  Current options:
% 15.37/2.49  ------ 
% 15.37/2.49  
% 15.37/2.49  ------ Input Options
% 15.37/2.49  
% 15.37/2.49  --out_options                           all
% 15.37/2.49  --tptp_safe_out                         true
% 15.37/2.49  --problem_path                          ""
% 15.37/2.49  --include_path                          ""
% 15.37/2.49  --clausifier                            res/vclausify_rel
% 15.37/2.49  --clausifier_options                    ""
% 15.37/2.49  --stdin                                 false
% 15.37/2.49  --stats_out                             all
% 15.37/2.49  
% 15.37/2.49  ------ General Options
% 15.37/2.49  
% 15.37/2.49  --fof                                   false
% 15.37/2.49  --time_out_real                         305.
% 15.37/2.49  --time_out_virtual                      -1.
% 15.37/2.49  --symbol_type_check                     false
% 15.37/2.49  --clausify_out                          false
% 15.37/2.49  --sig_cnt_out                           false
% 15.37/2.49  --trig_cnt_out                          false
% 15.37/2.49  --trig_cnt_out_tolerance                1.
% 15.37/2.49  --trig_cnt_out_sk_spl                   false
% 15.37/2.49  --abstr_cl_out                          false
% 15.37/2.49  
% 15.37/2.49  ------ Global Options
% 15.37/2.49  
% 15.37/2.49  --schedule                              default
% 15.37/2.49  --add_important_lit                     false
% 15.37/2.49  --prop_solver_per_cl                    1000
% 15.37/2.49  --min_unsat_core                        false
% 15.37/2.49  --soft_assumptions                      false
% 15.37/2.49  --soft_lemma_size                       3
% 15.37/2.49  --prop_impl_unit_size                   0
% 15.37/2.49  --prop_impl_unit                        []
% 15.37/2.49  --share_sel_clauses                     true
% 15.37/2.49  --reset_solvers                         false
% 15.37/2.49  --bc_imp_inh                            [conj_cone]
% 15.37/2.49  --conj_cone_tolerance                   3.
% 15.37/2.49  --extra_neg_conj                        none
% 15.37/2.49  --large_theory_mode                     true
% 15.37/2.49  --prolific_symb_bound                   200
% 15.37/2.49  --lt_threshold                          2000
% 15.37/2.49  --clause_weak_htbl                      true
% 15.37/2.49  --gc_record_bc_elim                     false
% 15.37/2.49  
% 15.37/2.49  ------ Preprocessing Options
% 15.37/2.49  
% 15.37/2.49  --preprocessing_flag                    true
% 15.37/2.49  --time_out_prep_mult                    0.1
% 15.37/2.49  --splitting_mode                        input
% 15.37/2.49  --splitting_grd                         true
% 15.37/2.49  --splitting_cvd                         false
% 15.37/2.49  --splitting_cvd_svl                     false
% 15.37/2.49  --splitting_nvd                         32
% 15.37/2.49  --sub_typing                            true
% 15.37/2.49  --prep_gs_sim                           true
% 15.37/2.49  --prep_unflatten                        true
% 15.37/2.49  --prep_res_sim                          true
% 15.37/2.49  --prep_upred                            true
% 15.37/2.49  --prep_sem_filter                       exhaustive
% 15.37/2.49  --prep_sem_filter_out                   false
% 15.37/2.49  --pred_elim                             true
% 15.37/2.49  --res_sim_input                         true
% 15.37/2.49  --eq_ax_congr_red                       true
% 15.37/2.49  --pure_diseq_elim                       true
% 15.37/2.49  --brand_transform                       false
% 15.37/2.49  --non_eq_to_eq                          false
% 15.37/2.49  --prep_def_merge                        true
% 15.37/2.49  --prep_def_merge_prop_impl              false
% 15.37/2.49  --prep_def_merge_mbd                    true
% 15.37/2.49  --prep_def_merge_tr_red                 false
% 15.37/2.49  --prep_def_merge_tr_cl                  false
% 15.37/2.49  --smt_preprocessing                     true
% 15.37/2.49  --smt_ac_axioms                         fast
% 15.37/2.49  --preprocessed_out                      false
% 15.37/2.49  --preprocessed_stats                    false
% 15.37/2.49  
% 15.37/2.49  ------ Abstraction refinement Options
% 15.37/2.49  
% 15.37/2.49  --abstr_ref                             []
% 15.37/2.49  --abstr_ref_prep                        false
% 15.37/2.49  --abstr_ref_until_sat                   false
% 15.37/2.49  --abstr_ref_sig_restrict                funpre
% 15.37/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.37/2.49  --abstr_ref_under                       []
% 15.37/2.49  
% 15.37/2.49  ------ SAT Options
% 15.37/2.49  
% 15.37/2.49  --sat_mode                              false
% 15.37/2.49  --sat_fm_restart_options                ""
% 15.37/2.49  --sat_gr_def                            false
% 15.37/2.49  --sat_epr_types                         true
% 15.37/2.49  --sat_non_cyclic_types                  false
% 15.37/2.49  --sat_finite_models                     false
% 15.37/2.49  --sat_fm_lemmas                         false
% 15.37/2.49  --sat_fm_prep                           false
% 15.37/2.49  --sat_fm_uc_incr                        true
% 15.37/2.49  --sat_out_model                         small
% 15.37/2.49  --sat_out_clauses                       false
% 15.37/2.49  
% 15.37/2.49  ------ QBF Options
% 15.37/2.49  
% 15.37/2.49  --qbf_mode                              false
% 15.37/2.49  --qbf_elim_univ                         false
% 15.37/2.49  --qbf_dom_inst                          none
% 15.37/2.49  --qbf_dom_pre_inst                      false
% 15.37/2.49  --qbf_sk_in                             false
% 15.37/2.49  --qbf_pred_elim                         true
% 15.37/2.49  --qbf_split                             512
% 15.37/2.49  
% 15.37/2.49  ------ BMC1 Options
% 15.37/2.49  
% 15.37/2.49  --bmc1_incremental                      false
% 15.37/2.49  --bmc1_axioms                           reachable_all
% 15.37/2.49  --bmc1_min_bound                        0
% 15.37/2.49  --bmc1_max_bound                        -1
% 15.37/2.49  --bmc1_max_bound_default                -1
% 15.37/2.49  --bmc1_symbol_reachability              true
% 15.37/2.49  --bmc1_property_lemmas                  false
% 15.37/2.49  --bmc1_k_induction                      false
% 15.37/2.49  --bmc1_non_equiv_states                 false
% 15.37/2.49  --bmc1_deadlock                         false
% 15.37/2.49  --bmc1_ucm                              false
% 15.37/2.49  --bmc1_add_unsat_core                   none
% 15.37/2.49  --bmc1_unsat_core_children              false
% 15.37/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.37/2.49  --bmc1_out_stat                         full
% 15.37/2.49  --bmc1_ground_init                      false
% 15.37/2.49  --bmc1_pre_inst_next_state              false
% 15.37/2.49  --bmc1_pre_inst_state                   false
% 15.37/2.49  --bmc1_pre_inst_reach_state             false
% 15.37/2.49  --bmc1_out_unsat_core                   false
% 15.37/2.49  --bmc1_aig_witness_out                  false
% 15.37/2.49  --bmc1_verbose                          false
% 15.37/2.49  --bmc1_dump_clauses_tptp                false
% 15.37/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.37/2.49  --bmc1_dump_file                        -
% 15.37/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.37/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.37/2.49  --bmc1_ucm_extend_mode                  1
% 15.37/2.49  --bmc1_ucm_init_mode                    2
% 15.37/2.49  --bmc1_ucm_cone_mode                    none
% 15.37/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.37/2.49  --bmc1_ucm_relax_model                  4
% 15.37/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.37/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.37/2.49  --bmc1_ucm_layered_model                none
% 15.37/2.49  --bmc1_ucm_max_lemma_size               10
% 15.37/2.49  
% 15.37/2.49  ------ AIG Options
% 15.37/2.49  
% 15.37/2.49  --aig_mode                              false
% 15.37/2.49  
% 15.37/2.49  ------ Instantiation Options
% 15.37/2.49  
% 15.37/2.49  --instantiation_flag                    true
% 15.37/2.49  --inst_sos_flag                         true
% 15.37/2.49  --inst_sos_phase                        true
% 15.37/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.37/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.37/2.49  --inst_lit_sel_side                     none
% 15.37/2.49  --inst_solver_per_active                1400
% 15.37/2.49  --inst_solver_calls_frac                1.
% 15.37/2.49  --inst_passive_queue_type               priority_queues
% 15.37/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.37/2.49  --inst_passive_queues_freq              [25;2]
% 15.37/2.49  --inst_dismatching                      true
% 15.37/2.49  --inst_eager_unprocessed_to_passive     true
% 15.37/2.49  --inst_prop_sim_given                   true
% 15.37/2.49  --inst_prop_sim_new                     false
% 15.37/2.49  --inst_subs_new                         false
% 15.37/2.49  --inst_eq_res_simp                      false
% 15.37/2.49  --inst_subs_given                       false
% 15.37/2.49  --inst_orphan_elimination               true
% 15.37/2.49  --inst_learning_loop_flag               true
% 15.37/2.49  --inst_learning_start                   3000
% 15.37/2.49  --inst_learning_factor                  2
% 15.37/2.49  --inst_start_prop_sim_after_learn       3
% 15.37/2.49  --inst_sel_renew                        solver
% 15.37/2.49  --inst_lit_activity_flag                true
% 15.37/2.49  --inst_restr_to_given                   false
% 15.37/2.49  --inst_activity_threshold               500
% 15.37/2.49  --inst_out_proof                        true
% 15.37/2.49  
% 15.37/2.49  ------ Resolution Options
% 15.37/2.49  
% 15.37/2.49  --resolution_flag                       false
% 15.37/2.49  --res_lit_sel                           adaptive
% 15.37/2.49  --res_lit_sel_side                      none
% 15.37/2.49  --res_ordering                          kbo
% 15.37/2.49  --res_to_prop_solver                    active
% 15.37/2.49  --res_prop_simpl_new                    false
% 15.37/2.49  --res_prop_simpl_given                  true
% 15.37/2.49  --res_passive_queue_type                priority_queues
% 15.37/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.37/2.49  --res_passive_queues_freq               [15;5]
% 15.37/2.49  --res_forward_subs                      full
% 15.37/2.49  --res_backward_subs                     full
% 15.37/2.49  --res_forward_subs_resolution           true
% 15.37/2.49  --res_backward_subs_resolution          true
% 15.37/2.49  --res_orphan_elimination                true
% 15.37/2.49  --res_time_limit                        2.
% 15.37/2.49  --res_out_proof                         true
% 15.37/2.49  
% 15.37/2.49  ------ Superposition Options
% 15.37/2.49  
% 15.37/2.49  --superposition_flag                    true
% 15.37/2.49  --sup_passive_queue_type                priority_queues
% 15.37/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.37/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.37/2.49  --demod_completeness_check              fast
% 15.37/2.49  --demod_use_ground                      true
% 15.37/2.49  --sup_to_prop_solver                    passive
% 15.37/2.49  --sup_prop_simpl_new                    true
% 15.37/2.49  --sup_prop_simpl_given                  true
% 15.37/2.49  --sup_fun_splitting                     true
% 15.37/2.49  --sup_smt_interval                      50000
% 15.37/2.49  
% 15.37/2.49  ------ Superposition Simplification Setup
% 15.37/2.49  
% 15.37/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.37/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.37/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.37/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.37/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.37/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.37/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.37/2.49  --sup_immed_triv                        [TrivRules]
% 15.37/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_immed_bw_main                     []
% 15.37/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.37/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.37/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.37/2.49  --sup_input_bw                          []
% 15.37/2.49  
% 15.37/2.49  ------ Combination Options
% 15.37/2.49  
% 15.37/2.49  --comb_res_mult                         3
% 15.37/2.49  --comb_sup_mult                         2
% 15.37/2.49  --comb_inst_mult                        10
% 15.37/2.49  
% 15.37/2.49  ------ Debug Options
% 15.37/2.49  
% 15.37/2.49  --dbg_backtrace                         false
% 15.37/2.49  --dbg_dump_prop_clauses                 false
% 15.37/2.49  --dbg_dump_prop_clauses_file            -
% 15.37/2.49  --dbg_out_stat                          false
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  ------ Proving...
% 15.37/2.49  
% 15.37/2.49  
% 15.37/2.49  % SZS status Theorem for theBenchmark.p
% 15.37/2.49  
% 15.37/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.37/2.49  
% 15.37/2.49  fof(f3,axiom,(
% 15.37/2.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f43,plain,(
% 15.37/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 15.37/2.49    inference(nnf_transformation,[],[f3])).
% 15.37/2.49  
% 15.37/2.49  fof(f44,plain,(
% 15.37/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.37/2.49    inference(rectify,[],[f43])).
% 15.37/2.49  
% 15.37/2.49  fof(f47,plain,(
% 15.37/2.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f46,plain,(
% 15.37/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f45,plain,(
% 15.37/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f48,plain,(
% 15.37/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.37/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).
% 15.37/2.49  
% 15.37/2.49  fof(f74,plain,(
% 15.37/2.49    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  fof(f9,axiom,(
% 15.37/2.49    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f51,plain,(
% 15.37/2.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.37/2.49    inference(nnf_transformation,[],[f9])).
% 15.37/2.49  
% 15.37/2.49  fof(f52,plain,(
% 15.37/2.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.37/2.49    inference(flattening,[],[f51])).
% 15.37/2.49  
% 15.37/2.49  fof(f83,plain,(
% 15.37/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 15.37/2.49    inference(cnf_transformation,[],[f52])).
% 15.37/2.49  
% 15.37/2.49  fof(f5,axiom,(
% 15.37/2.49    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f77,plain,(
% 15.37/2.49    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 15.37/2.49    inference(cnf_transformation,[],[f5])).
% 15.37/2.49  
% 15.37/2.49  fof(f106,plain,(
% 15.37/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.37/2.49    inference(definition_unfolding,[],[f83,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f85,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 15.37/2.49    inference(cnf_transformation,[],[f52])).
% 15.37/2.49  
% 15.37/2.49  fof(f104,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 15.37/2.49    inference(definition_unfolding,[],[f85,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f118,plain,(
% 15.37/2.49    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.37/2.49    inference(equality_resolution,[],[f104])).
% 15.37/2.49  
% 15.37/2.49  fof(f18,conjecture,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f19,negated_conjecture,(
% 15.37/2.49    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.37/2.49    inference(negated_conjecture,[],[f18])).
% 15.37/2.49  
% 15.37/2.49  fof(f35,plain,(
% 15.37/2.49    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.37/2.49    inference(ennf_transformation,[],[f19])).
% 15.37/2.49  
% 15.37/2.49  fof(f36,plain,(
% 15.37/2.49    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.37/2.49    inference(flattening,[],[f35])).
% 15.37/2.49  
% 15.37/2.49  fof(f58,plain,(
% 15.37/2.49    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 15.37/2.49    inference(nnf_transformation,[],[f36])).
% 15.37/2.49  
% 15.37/2.49  fof(f59,plain,(
% 15.37/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.37/2.49    inference(flattening,[],[f58])).
% 15.37/2.49  
% 15.37/2.49  fof(f60,plain,(
% 15.37/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.37/2.49    inference(rectify,[],[f59])).
% 15.37/2.49  
% 15.37/2.49  fof(f62,plain,(
% 15.37/2.49    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f61,plain,(
% 15.37/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f63,plain,(
% 15.37/2.49    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 15.37/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f62,f61])).
% 15.37/2.49  
% 15.37/2.49  fof(f99,plain,(
% 15.37/2.49    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f63])).
% 15.37/2.49  
% 15.37/2.49  fof(f112,plain,(
% 15.37/2.49    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 15.37/2.49    inference(definition_unfolding,[],[f99,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f72,plain,(
% 15.37/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  fof(f115,plain,(
% 15.37/2.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 15.37/2.49    inference(equality_resolution,[],[f72])).
% 15.37/2.49  
% 15.37/2.49  fof(f17,axiom,(
% 15.37/2.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f34,plain,(
% 15.37/2.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 15.37/2.49    inference(ennf_transformation,[],[f17])).
% 15.37/2.49  
% 15.37/2.49  fof(f97,plain,(
% 15.37/2.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f34])).
% 15.37/2.49  
% 15.37/2.49  fof(f98,plain,(
% 15.37/2.49    v3_ordinal1(sK6)),
% 15.37/2.49    inference(cnf_transformation,[],[f63])).
% 15.37/2.49  
% 15.37/2.49  fof(f6,axiom,(
% 15.37/2.49    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f49,plain,(
% 15.37/2.49    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 15.37/2.49    inference(nnf_transformation,[],[f6])).
% 15.37/2.49  
% 15.37/2.49  fof(f79,plain,(
% 15.37/2.49    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 15.37/2.49    inference(cnf_transformation,[],[f49])).
% 15.37/2.49  
% 15.37/2.49  fof(f12,axiom,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f27,plain,(
% 15.37/2.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(ennf_transformation,[],[f12])).
% 15.37/2.49  
% 15.37/2.49  fof(f28,plain,(
% 15.37/2.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(flattening,[],[f27])).
% 15.37/2.49  
% 15.37/2.49  fof(f88,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f28])).
% 15.37/2.49  
% 15.37/2.49  fof(f7,axiom,(
% 15.37/2.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f23,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 15.37/2.49    inference(ennf_transformation,[],[f7])).
% 15.37/2.49  
% 15.37/2.49  fof(f24,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(flattening,[],[f23])).
% 15.37/2.49  
% 15.37/2.49  fof(f50,plain,(
% 15.37/2.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(nnf_transformation,[],[f24])).
% 15.37/2.49  
% 15.37/2.49  fof(f80,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f50])).
% 15.37/2.49  
% 15.37/2.49  fof(f70,plain,(
% 15.37/2.49    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  fof(f117,plain,(
% 15.37/2.49    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.37/2.49    inference(equality_resolution,[],[f70])).
% 15.37/2.49  
% 15.37/2.49  fof(f71,plain,(
% 15.37/2.49    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  fof(f116,plain,(
% 15.37/2.49    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.37/2.49    inference(equality_resolution,[],[f71])).
% 15.37/2.49  
% 15.37/2.49  fof(f11,axiom,(
% 15.37/2.49    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f25,plain,(
% 15.37/2.49    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 15.37/2.49    inference(ennf_transformation,[],[f11])).
% 15.37/2.49  
% 15.37/2.49  fof(f26,plain,(
% 15.37/2.49    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 15.37/2.49    inference(flattening,[],[f25])).
% 15.37/2.49  
% 15.37/2.49  fof(f87,plain,(
% 15.37/2.49    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f26])).
% 15.37/2.49  
% 15.37/2.49  fof(f4,axiom,(
% 15.37/2.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f21,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 15.37/2.49    inference(ennf_transformation,[],[f4])).
% 15.37/2.49  
% 15.37/2.49  fof(f22,plain,(
% 15.37/2.49    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(flattening,[],[f21])).
% 15.37/2.49  
% 15.37/2.49  fof(f76,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f22])).
% 15.37/2.49  
% 15.37/2.49  fof(f2,axiom,(
% 15.37/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f41,plain,(
% 15.37/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.49    inference(nnf_transformation,[],[f2])).
% 15.37/2.49  
% 15.37/2.49  fof(f42,plain,(
% 15.37/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.37/2.49    inference(flattening,[],[f41])).
% 15.37/2.49  
% 15.37/2.49  fof(f67,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.37/2.49    inference(cnf_transformation,[],[f42])).
% 15.37/2.49  
% 15.37/2.49  fof(f114,plain,(
% 15.37/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.37/2.49    inference(equality_resolution,[],[f67])).
% 15.37/2.49  
% 15.37/2.49  fof(f84,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f52])).
% 15.37/2.49  
% 15.37/2.49  fof(f105,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 15.37/2.49    inference(definition_unfolding,[],[f84,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f15,axiom,(
% 15.37/2.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f31,plain,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 15.37/2.49    inference(ennf_transformation,[],[f15])).
% 15.37/2.49  
% 15.37/2.49  fof(f54,plain,(
% 15.37/2.49    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f55,plain,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 15.37/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f54])).
% 15.37/2.49  
% 15.37/2.49  fof(f92,plain,(
% 15.37/2.49    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f55])).
% 15.37/2.49  
% 15.37/2.49  fof(f93,plain,(
% 15.37/2.49    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 15.37/2.49    inference(cnf_transformation,[],[f55])).
% 15.37/2.49  
% 15.37/2.49  fof(f13,axiom,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f29,plain,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(ennf_transformation,[],[f13])).
% 15.37/2.49  
% 15.37/2.49  fof(f89,plain,(
% 15.37/2.49    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f29])).
% 15.37/2.49  
% 15.37/2.49  fof(f108,plain,(
% 15.37/2.49    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(definition_unfolding,[],[f89,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f102,plain,(
% 15.37/2.49    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 15.37/2.49    inference(cnf_transformation,[],[f63])).
% 15.37/2.49  
% 15.37/2.49  fof(f111,plain,(
% 15.37/2.49    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 15.37/2.49    inference(definition_unfolding,[],[f102,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f100,plain,(
% 15.37/2.49    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 15.37/2.49    inference(cnf_transformation,[],[f63])).
% 15.37/2.49  
% 15.37/2.49  fof(f101,plain,(
% 15.37/2.49    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 15.37/2.49    inference(cnf_transformation,[],[f63])).
% 15.37/2.49  
% 15.37/2.49  fof(f14,axiom,(
% 15.37/2.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f30,plain,(
% 15.37/2.49    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(ennf_transformation,[],[f14])).
% 15.37/2.49  
% 15.37/2.49  fof(f53,plain,(
% 15.37/2.49    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.37/2.49    inference(nnf_transformation,[],[f30])).
% 15.37/2.49  
% 15.37/2.49  fof(f90,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f53])).
% 15.37/2.49  
% 15.37/2.49  fof(f110,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.37/2.49    inference(definition_unfolding,[],[f90,f77])).
% 15.37/2.49  
% 15.37/2.49  fof(f78,plain,(
% 15.37/2.49    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f49])).
% 15.37/2.49  
% 15.37/2.49  fof(f1,axiom,(
% 15.37/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.37/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.37/2.49  
% 15.37/2.49  fof(f20,plain,(
% 15.37/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.37/2.49    inference(ennf_transformation,[],[f1])).
% 15.37/2.49  
% 15.37/2.49  fof(f37,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.49    inference(nnf_transformation,[],[f20])).
% 15.37/2.49  
% 15.37/2.49  fof(f38,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.49    inference(rectify,[],[f37])).
% 15.37/2.49  
% 15.37/2.49  fof(f39,plain,(
% 15.37/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.37/2.49    introduced(choice_axiom,[])).
% 15.37/2.49  
% 15.37/2.49  fof(f40,plain,(
% 15.37/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.37/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 15.37/2.49  
% 15.37/2.49  fof(f65,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f40])).
% 15.37/2.49  
% 15.37/2.49  fof(f66,plain,(
% 15.37/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f40])).
% 15.37/2.49  
% 15.37/2.49  fof(f64,plain,(
% 15.37/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f40])).
% 15.37/2.49  
% 15.37/2.49  fof(f75,plain,(
% 15.37/2.49    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  fof(f73,plain,(
% 15.37/2.49    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.37/2.49    inference(cnf_transformation,[],[f48])).
% 15.37/2.49  
% 15.37/2.49  cnf(c_7,plain,
% 15.37/2.49      ( r2_hidden(sK2(X0,X1),X0)
% 15.37/2.49      | r2_hidden(sK1(X0,X1),X1)
% 15.37/2.49      | k3_tarski(X0) = X1 ),
% 15.37/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1719,plain,
% 15.37/2.49      ( k3_tarski(X0) = X1
% 15.37/2.49      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 15.37/2.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_20,plain,
% 15.37/2.49      ( r2_hidden(X0,X1)
% 15.37/2.49      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.37/2.49      | X1 = X0 ),
% 15.37/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1707,plain,
% 15.37/2.49      ( X0 = X1
% 15.37/2.49      | r2_hidden(X1,X0) = iProver_top
% 15.37/2.49      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_4561,plain,
% 15.37/2.49      ( sK2(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 15.37/2.49      | k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
% 15.37/2.49      | r2_hidden(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
% 15.37/2.49      | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1719,c_1707]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_18,plain,
% 15.37/2.49      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.37/2.49      inference(cnf_transformation,[],[f118]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1709,plain,
% 15.37/2.49      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_36,negated_conjecture,
% 15.37/2.49      ( ~ r2_hidden(X0,sK6)
% 15.37/2.49      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 15.37/2.49      | v4_ordinal1(sK6)
% 15.37/2.49      | ~ v3_ordinal1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f112]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1692,plain,
% 15.37/2.49      ( r2_hidden(X0,sK6) != iProver_top
% 15.37/2.49      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_9,plain,
% 15.37/2.49      ( ~ r2_hidden(X0,X1)
% 15.37/2.49      | ~ r2_hidden(X2,X0)
% 15.37/2.49      | r2_hidden(X2,k3_tarski(X1)) ),
% 15.37/2.49      inference(cnf_transformation,[],[f115]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1717,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.37/2.49      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_4533,plain,
% 15.37/2.49      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.37/2.49      | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.37/2.49      | r2_hidden(X1,sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(X1) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1692,c_1717]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5023,plain,
% 15.37/2.49      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.37/2.49      | r2_hidden(X0,sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1709,c_4533]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_32,plain,
% 15.37/2.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1696,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_6392,plain,
% 15.37/2.49      ( r2_hidden(X0,sK6) != iProver_top
% 15.37/2.49      | r1_tarski(k3_tarski(sK6),X0) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_5023,c_1696]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_37,negated_conjecture,
% 15.37/2.49      ( v3_ordinal1(sK6) ),
% 15.37/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_38,plain,
% 15.37/2.49      ( v3_ordinal1(sK6) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_13,plain,
% 15.37/2.49      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.37/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_96,plain,
% 15.37/2.49      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_98,plain,
% 15.37/2.49      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_96]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_23,plain,
% 15.37/2.49      ( r2_hidden(X0,X1)
% 15.37/2.49      | r2_hidden(X1,X0)
% 15.37/2.49      | ~ v3_ordinal1(X1)
% 15.37/2.49      | ~ v3_ordinal1(X0)
% 15.37/2.49      | X1 = X0 ),
% 15.37/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1919,plain,
% 15.37/2.49      ( r2_hidden(k3_tarski(sK6),sK6)
% 15.37/2.49      | r2_hidden(sK6,k3_tarski(sK6))
% 15.37/2.49      | ~ v3_ordinal1(k3_tarski(sK6))
% 15.37/2.49      | ~ v3_ordinal1(sK6)
% 15.37/2.49      | k3_tarski(sK6) = sK6 ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_23]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1926,plain,
% 15.37/2.49      ( k3_tarski(sK6) = sK6
% 15.37/2.49      | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 15.37/2.49      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_16,plain,
% 15.37/2.49      ( ~ r1_ordinal1(X0,X1)
% 15.37/2.49      | r1_tarski(X0,X1)
% 15.37/2.49      | ~ v3_ordinal1(X1)
% 15.37/2.49      | ~ v3_ordinal1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2392,plain,
% 15.37/2.49      ( ~ r1_ordinal1(sK3(X0,X1),sK6)
% 15.37/2.49      | r1_tarski(sK3(X0,X1),sK6)
% 15.37/2.49      | ~ v3_ordinal1(sK3(X0,X1))
% 15.37/2.49      | ~ v3_ordinal1(sK6) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2403,plain,
% 15.37/2.49      ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
% 15.37/2.49      | r1_tarski(sK3(X0,X1),sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2405,plain,
% 15.37/2.49      ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
% 15.37/2.49      | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_2403]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2646,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6)
% 15.37/2.49      | ~ r2_hidden(k3_tarski(sK6),sK6)
% 15.37/2.49      | v4_ordinal1(sK6)
% 15.37/2.49      | ~ v3_ordinal1(k3_tarski(sK6)) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_36]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2647,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) = iProver_top
% 15.37/2.49      | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_11,plain,
% 15.37/2.49      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 15.37/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1715,plain,
% 15.37/2.49      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 15.37/2.49      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2972,plain,
% 15.37/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.37/2.49      | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1715,c_1696]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2974,plain,
% 15.37/2.49      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 15.37/2.49      | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_2972]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10,plain,
% 15.37/2.49      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 15.37/2.49      inference(cnf_transformation,[],[f116]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1716,plain,
% 15.37/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.37/2.49      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3124,plain,
% 15.37/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.37/2.49      | r1_tarski(X1,sK3(X1,X0)) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1716,c_1696]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3126,plain,
% 15.37/2.49      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 15.37/2.49      | r1_tarski(sK6,sK3(sK6,sK6)) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_3124]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_22,plain,
% 15.37/2.49      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1706,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | v3_ordinal1(X1) != iProver_top
% 15.37/2.49      | v3_ordinal1(X0) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3837,plain,
% 15.37/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.37/2.49      | v3_ordinal1(X1) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1716,c_1706]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3846,plain,
% 15.37/2.49      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_3837]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5452,plain,
% 15.37/2.49      ( ~ r1_ordinal1(X0,sK3(sK6,X1))
% 15.37/2.49      | r1_tarski(X0,sK3(sK6,X1))
% 15.37/2.49      | ~ v3_ordinal1(X0)
% 15.37/2.49      | ~ v3_ordinal1(sK3(sK6,X1)) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5463,plain,
% 15.37/2.49      ( r1_ordinal1(X0,sK3(sK6,X1)) != iProver_top
% 15.37/2.49      | r1_tarski(X0,sK3(sK6,X1)) = iProver_top
% 15.37/2.49      | v3_ordinal1(X0) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(sK6,X1)) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_5452]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5465,plain,
% 15.37/2.49      ( r1_ordinal1(sK6,sK3(sK6,sK6)) != iProver_top
% 15.37/2.49      | r1_tarski(sK6,sK3(sK6,sK6)) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_5463]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_12,plain,
% 15.37/2.49      ( r1_ordinal1(X0,X1)
% 15.37/2.49      | r1_ordinal1(X1,X0)
% 15.37/2.49      | ~ v3_ordinal1(X1)
% 15.37/2.49      | ~ v3_ordinal1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5587,plain,
% 15.37/2.49      ( r1_ordinal1(sK3(X0,X1),sK6)
% 15.37/2.49      | r1_ordinal1(sK6,sK3(X0,X1))
% 15.37/2.49      | ~ v3_ordinal1(sK3(X0,X1))
% 15.37/2.49      | ~ v3_ordinal1(sK6) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5588,plain,
% 15.37/2.49      ( r1_ordinal1(sK3(X0,X1),sK6) = iProver_top
% 15.37/2.49      | r1_ordinal1(sK6,sK3(X0,X1)) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_5587]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5590,plain,
% 15.37/2.49      ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
% 15.37/2.49      | r1_ordinal1(sK6,sK3(sK6,sK6)) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_5588]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5,plain,
% 15.37/2.49      ( r1_tarski(X0,X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1721,plain,
% 15.37/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_19,plain,
% 15.37/2.49      ( ~ r2_hidden(X0,X1)
% 15.37/2.49      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 15.37/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1708,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_2826,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1708,c_1696]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3496,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1721,c_2826]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_6396,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) = iProver_top
% 15.37/2.49      | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_5023,c_3496]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_28,plain,
% 15.37/2.49      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 15.37/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1700,plain,
% 15.37/2.49      ( r2_hidden(sK4(X0),X0) = iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_3841,plain,
% 15.37/2.49      ( v3_ordinal1(X0) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK4(X0)) = iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1700,c_1706]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_27,plain,
% 15.37/2.49      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 15.37/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_60,plain,
% 15.37/2.49      ( v3_ordinal1(sK4(X0)) != iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_8682,plain,
% 15.37/2.49      ( v3_ordinal1(X0) != iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.37/2.49      inference(global_propositional_subsumption,
% 15.37/2.49                [status(thm)],
% 15.37/2.49                [c_3841,c_60]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_8685,plain,
% 15.37/2.49      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_8682]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_24,plain,
% 15.37/2.49      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.37/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10566,plain,
% 15.37/2.49      ( v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))))
% 15.37/2.49      | ~ v3_ordinal1(k3_tarski(sK6)) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_24]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10567,plain,
% 15.37/2.49      ( v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) = iProver_top
% 15.37/2.49      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_10566]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_10943,plain,
% 15.37/2.49      ( v4_ordinal1(sK6) = iProver_top ),
% 15.37/2.49      inference(global_propositional_subsumption,
% 15.37/2.49                [status(thm)],
% 15.37/2.49                [c_6392,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,
% 15.37/2.49                 c_3846,c_5465,c_5590,c_6396,c_8685,c_10567]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1705,plain,
% 15.37/2.49      ( X0 = X1
% 15.37/2.49      | r2_hidden(X1,X0) = iProver_top
% 15.37/2.49      | r2_hidden(X0,X1) = iProver_top
% 15.37/2.49      | v3_ordinal1(X1) != iProver_top
% 15.37/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_33,negated_conjecture,
% 15.37/2.49      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 15.37/2.49      | ~ v4_ordinal1(sK6) ),
% 15.37/2.49      inference(cnf_transformation,[],[f111]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_1695,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_5531,plain,
% 15.37/2.49      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.37/2.49      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) != iProver_top
% 15.37/2.49      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(superposition,[status(thm)],[c_1705,c_1695]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_35,negated_conjecture,
% 15.37/2.49      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 15.37/2.49      inference(cnf_transformation,[],[f100]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_42,plain,
% 15.37/2.49      ( v4_ordinal1(sK6) != iProver_top
% 15.37/2.49      | v3_ordinal1(sK7) = iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_34,negated_conjecture,
% 15.37/2.49      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 15.37/2.49      inference(cnf_transformation,[],[f101]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_43,plain,
% 15.37/2.49      ( r2_hidden(sK7,sK6) = iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_44,plain,
% 15.37/2.49      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 15.37/2.49      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_46,plain,
% 15.37/2.49      ( ~ r2_hidden(sK6,sK6) | ~ r1_tarski(sK6,sK6) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_32]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_45,plain,
% 15.37/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.37/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_47,plain,
% 15.37/2.49      ( r2_hidden(sK6,sK6) != iProver_top
% 15.37/2.49      | r1_tarski(sK6,sK6) != iProver_top ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_45]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_26,plain,
% 15.37/2.49      ( r1_ordinal1(X0,X1)
% 15.37/2.49      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.37/2.49      | ~ v3_ordinal1(X1)
% 15.37/2.49      | ~ v3_ordinal1(X0) ),
% 15.37/2.49      inference(cnf_transformation,[],[f110]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_64,plain,
% 15.37/2.49      ( r1_ordinal1(sK6,sK6)
% 15.37/2.49      | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
% 15.37/2.49      | ~ v3_ordinal1(sK6) ),
% 15.37/2.49      inference(instantiation,[status(thm)],[c_26]) ).
% 15.37/2.49  
% 15.37/2.49  cnf(c_63,plain,
% 15.37/2.49      ( r1_ordinal1(X0,X1) = iProver_top
% 15.37/2.49      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(X1) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_65,plain,
% 15.37/2.50      ( r1_ordinal1(sK6,sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.37/2.50      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_63]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_73,plain,
% 15.37/2.50      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_23]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_84,plain,
% 15.37/2.50      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_18]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_83,plain,
% 15.37/2.50      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_85,plain,
% 15.37/2.50      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_83]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_88,plain,
% 15.37/2.50      ( ~ r1_ordinal1(sK6,sK6)
% 15.37/2.50      | r1_tarski(sK6,sK6)
% 15.37/2.50      | ~ v3_ordinal1(sK6) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_16]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_87,plain,
% 15.37/2.50      ( r1_ordinal1(X0,X1) != iProver_top
% 15.37/2.50      | r1_tarski(X0,X1) = iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(X1) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_89,plain,
% 15.37/2.50      ( r1_ordinal1(sK6,sK6) != iProver_top
% 15.37/2.50      | r1_tarski(sK6,sK6) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_87]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1819,plain,
% 15.37/2.50      ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.37/2.50      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
% 15.37/2.50      | ~ v3_ordinal1(X0)
% 15.37/2.50      | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.37/2.50      | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_23]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1830,plain,
% 15.37/2.50      ( k2_xboole_0(sK7,k1_tarski(sK7)) = X0
% 15.37/2.50      | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.37/2.50      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_1819]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1832,plain,
% 15.37/2.50      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.37/2.50      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.37/2.50      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.37/2.50      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_1830]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_994,plain,
% 15.37/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.37/2.50      theory(equality) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1871,plain,
% 15.37/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_994]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2114,plain,
% 15.37/2.50      ( r2_hidden(X0,sK6)
% 15.37/2.50      | ~ r2_hidden(sK7,sK6)
% 15.37/2.50      | X0 != sK7
% 15.37/2.50      | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_1871]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2116,plain,
% 15.37/2.50      ( X0 != sK7
% 15.37/2.50      | sK6 != sK6
% 15.37/2.50      | r2_hidden(X0,sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_2114]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2118,plain,
% 15.37/2.50      ( sK6 != sK6
% 15.37/2.50      | sK6 != sK7
% 15.37/2.50      | r2_hidden(sK6,sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2116]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2271,plain,
% 15.37/2.50      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.37/2.50      | ~ v3_ordinal1(sK7) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_24]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2272,plain,
% 15.37/2.50      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK7) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_993,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2616,plain,
% 15.37/2.50      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_993]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2617,plain,
% 15.37/2.50      ( sK6 != sK6 | sK6 = sK7 | sK7 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2616]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_3528,plain,
% 15.37/2.50      ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.37/2.50      | r2_hidden(X0,sK7)
% 15.37/2.50      | sK7 = X0 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_20]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_3534,plain,
% 15.37/2.50      ( sK7 = X0
% 15.37/2.50      | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_3528]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_3536,plain,
% 15.37/2.50      ( sK7 = sK6
% 15.37/2.50      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.37/2.50      | r2_hidden(sK6,sK7) = iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_3534]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1694,plain,
% 15.37/2.50      ( r2_hidden(sK7,sK6) = iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_4532,plain,
% 15.37/2.50      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_1694,c_1717]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_4545,plain,
% 15.37/2.50      ( r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 15.37/2.50      | r2_hidden(sK6,sK7) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_4532]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_6142,plain,
% 15.37/2.50      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_5531,c_37,c_38,c_42,c_43,c_44,c_46,c_47,c_64,c_65,
% 15.37/2.50                 c_73,c_84,c_85,c_88,c_89,c_1832,c_2118,c_2272,c_2405,
% 15.37/2.50                 c_2617,c_2974,c_3126,c_3536,c_3846,c_4545,c_5465,c_5590]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_10948,plain,
% 15.37/2.50      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_10943,c_6142]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_11091,plain,
% 15.37/2.50      ( r2_hidden(X0,sK6) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_10948,c_1708]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_45299,plain,
% 15.37/2.50      ( sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = sK7
% 15.37/2.50      | k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
% 15.37/2.50      | r2_hidden(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_4561,c_11091]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_14,plain,
% 15.37/2.50      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 15.37/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1712,plain,
% 15.37/2.50      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_10947,plain,
% 15.37/2.50      ( k3_tarski(sK6) = sK6 ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_10943,c_1712]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_45315,plain,
% 15.37/2.50      ( sK2(sK6,X0) = sK7
% 15.37/2.50      | sK6 = X0
% 15.37/2.50      | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 15.37/2.50      inference(light_normalisation,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_45299,c_10947,c_10948]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1,plain,
% 15.37/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.37/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1724,plain,
% 15.37/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.37/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_0,plain,
% 15.37/2.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.37/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1725,plain,
% 15.37/2.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.37/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2825,plain,
% 15.37/2.50      ( r2_hidden(sK0(X0,k2_xboole_0(X1,k1_tarski(X1))),X1) != iProver_top
% 15.37/2.50      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_1708,c_1725]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_6527,plain,
% 15.37/2.50      ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_1724,c_2825]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2,plain,
% 15.37/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.37/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1723,plain,
% 15.37/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.37/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_4996,plain,
% 15.37/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | r1_tarski(k3_tarski(sK6),X1) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_4532,c_1723]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_6779,plain,
% 15.37/2.50      ( r2_hidden(X0,k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_6527,c_4996]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1702,plain,
% 15.37/2.50      ( r1_ordinal1(X0,X1) = iProver_top
% 15.37/2.50      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(X1) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_9782,plain,
% 15.37/2.50      ( r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_6779,c_1702]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_3840,plain,
% 15.37/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) = iProver_top
% 15.37/2.50      | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_1708,c_1706]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_16203,plain,
% 15.37/2.50      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_10948,c_3840]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_4997,plain,
% 15.37/2.50      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v4_ordinal1(sK6) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) = iProver_top
% 15.37/2.50      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_4532,c_1706]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_16983,plain,
% 15.37/2.50      ( v3_ordinal1(X0) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_16203,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,
% 15.37/2.50                 c_3846,c_4997,c_5465,c_5590,c_6396,c_8685,c_10567]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_16984,plain,
% 15.37/2.50      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) = iProver_top ),
% 15.37/2.50      inference(renaming,[status(thm)],[c_16983]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_34814,plain,
% 15.37/2.50      ( r2_hidden(X0,sK7) != iProver_top
% 15.37/2.50      | r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_9782,c_38,c_98,c_1926,c_2405,c_2647,c_2974,c_3126,
% 15.37/2.50                 c_3846,c_5465,c_5590,c_6396,c_8685,c_10567,c_16984]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_34815,plain,
% 15.37/2.50      ( r1_ordinal1(X0,k3_tarski(sK6)) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top ),
% 15.37/2.50      inference(renaming,[status(thm)],[c_34814]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_34818,plain,
% 15.37/2.50      ( r1_ordinal1(X0,sK6) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK7) != iProver_top ),
% 15.37/2.50      inference(light_normalisation,[status(thm)],[c_34815,c_10947]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_45941,plain,
% 15.37/2.50      ( sK2(sK6,sK7) = sK7
% 15.37/2.50      | sK6 = sK7
% 15.37/2.50      | r1_ordinal1(sK1(sK6,sK7),sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_45315,c_34818]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_93,plain,
% 15.37/2.50      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_95,plain,
% 15.37/2.50      ( k3_tarski(sK6) = sK6 | v4_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_93]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_290,plain,
% 15.37/2.50      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.37/2.50      inference(prop_impl,[status(thm)],[c_13]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_525,plain,
% 15.37/2.50      ( r2_hidden(sK7,sK6) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 15.37/2.50      inference(resolution_lifted,[status(thm)],[c_290,c_34]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_526,plain,
% 15.37/2.50      ( r2_hidden(sK7,sK6) | k3_tarski(sK6) != sK6 ),
% 15.37/2.50      inference(unflattening,[status(thm)],[c_525]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2428,plain,
% 15.37/2.50      ( k3_tarski(X0) != X1 | sK6 != X1 | sK6 = k3_tarski(X0) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_993]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2429,plain,
% 15.37/2.50      ( k3_tarski(sK6) != sK6 | sK6 = k3_tarski(sK6) | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2428]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2608,plain,
% 15.37/2.50      ( r2_hidden(k3_tarski(X0),sK6)
% 15.37/2.50      | ~ r2_hidden(sK7,sK6)
% 15.37/2.50      | k3_tarski(X0) != sK7
% 15.37/2.50      | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2114]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2610,plain,
% 15.37/2.50      ( r2_hidden(k3_tarski(sK6),sK6)
% 15.37/2.50      | ~ r2_hidden(sK7,sK6)
% 15.37/2.50      | k3_tarski(sK6) != sK7
% 15.37/2.50      | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2608]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2638,plain,
% 15.37/2.50      ( r2_hidden(X0,sK6)
% 15.37/2.50      | ~ r2_hidden(k3_tarski(sK6),sK6)
% 15.37/2.50      | X0 != k3_tarski(sK6)
% 15.37/2.50      | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_1871]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_2641,plain,
% 15.37/2.50      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 15.37/2.50      | r2_hidden(sK6,sK6)
% 15.37/2.50      | sK6 != k3_tarski(sK6)
% 15.37/2.50      | sK6 != sK6 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2638]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_27726,plain,
% 15.37/2.50      ( r2_hidden(sK2(X0,sK7),X0)
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7)
% 15.37/2.50      | k3_tarski(X0) = sK7 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_7]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_27728,plain,
% 15.37/2.50      ( k3_tarski(X0) = sK7
% 15.37/2.50      | r2_hidden(sK2(X0,sK7),X0) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_27726]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_27730,plain,
% 15.37/2.50      ( k3_tarski(sK6) = sK7
% 15.37/2.50      | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_27728]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_6,plain,
% 15.37/2.50      ( ~ r2_hidden(X0,X1)
% 15.37/2.50      | ~ r2_hidden(sK1(X1,X2),X0)
% 15.37/2.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 15.37/2.50      | k3_tarski(X1) = X2 ),
% 15.37/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_19524,plain,
% 15.37/2.50      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 15.37/2.50      | ~ r2_hidden(sK1(sK6,X0),sK7)
% 15.37/2.50      | ~ r2_hidden(sK7,sK6)
% 15.37/2.50      | k3_tarski(sK6) = X0 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_52180,plain,
% 15.37/2.50      ( ~ r2_hidden(sK1(sK6,sK7),sK7)
% 15.37/2.50      | ~ r2_hidden(sK7,sK6)
% 15.37/2.50      | k3_tarski(sK6) = sK7 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_19524]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_52189,plain,
% 15.37/2.50      ( k3_tarski(sK6) = sK7
% 15.37/2.50      | r2_hidden(sK1(sK6,sK7),sK7) != iProver_top
% 15.37/2.50      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_52180]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_58177,plain,
% 15.37/2.50      ( r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_45941,c_37,c_38,c_43,c_46,c_64,c_73,c_84,c_88,c_95,
% 15.37/2.50                 c_98,c_526,c_1926,c_2405,c_2429,c_2610,c_2641,c_2647,
% 15.37/2.50                 c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,
% 15.37/2.50                 c_10567,c_27730,c_52189]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_11089,plain,
% 15.37/2.50      ( r1_ordinal1(X0,sK7) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(sK7) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_10948,c_1702]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_13207,plain,
% 15.37/2.50      ( v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.37/2.50      | r1_ordinal1(X0,sK7) = iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_11089,c_38,c_42,c_98,c_1926,c_2405,c_2647,c_2974,
% 15.37/2.50                 c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,c_10567]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_13208,plain,
% 15.37/2.50      ( r1_ordinal1(X0,sK7) = iProver_top
% 15.37/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top ),
% 15.37/2.50      inference(renaming,[status(thm)],[c_13207]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_58189,plain,
% 15.37/2.50      ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK2(sK6,sK7)) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_58177,c_13208]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_10689,plain,
% 15.37/2.50      ( ~ r2_hidden(sK2(X0,X1),X2)
% 15.37/2.50      | ~ v3_ordinal1(X2)
% 15.37/2.50      | v3_ordinal1(sK2(X0,X1)) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_22]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_51135,plain,
% 15.37/2.50      ( ~ r2_hidden(sK2(sK6,sK7),sK6)
% 15.37/2.50      | v3_ordinal1(sK2(sK6,sK7))
% 15.37/2.50      | ~ v3_ordinal1(sK6) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_10689]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_51137,plain,
% 15.37/2.50      ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
% 15.37/2.50      | v3_ordinal1(sK2(sK6,sK7)) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK6) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_51135]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_58205,plain,
% 15.37/2.50      ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top ),
% 15.37/2.50      inference(global_propositional_subsumption,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_58189,c_37,c_38,c_43,c_46,c_64,c_73,c_84,c_88,c_95,
% 15.37/2.50                 c_98,c_526,c_1926,c_2405,c_2429,c_2610,c_2641,c_2647,
% 15.37/2.50                 c_2974,c_3126,c_3846,c_5465,c_5590,c_6396,c_8685,
% 15.37/2.50                 c_10567,c_27730,c_51137,c_52189]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_1710,plain,
% 15.37/2.50      ( r1_ordinal1(X0,X1) != iProver_top
% 15.37/2.50      | r1_tarski(X0,X1) = iProver_top
% 15.37/2.50      | v3_ordinal1(X0) != iProver_top
% 15.37/2.50      | v3_ordinal1(X1) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_58210,plain,
% 15.37/2.50      ( r1_tarski(sK2(sK6,sK7),sK7) = iProver_top
% 15.37/2.50      | v3_ordinal1(sK2(sK6,sK7)) != iProver_top
% 15.37/2.50      | v3_ordinal1(sK7) != iProver_top ),
% 15.37/2.50      inference(superposition,[status(thm)],[c_58205,c_1710]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_4308,plain,
% 15.37/2.50      ( r2_hidden(sK1(X0,X1),X2)
% 15.37/2.50      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 15.37/2.50      | ~ r1_tarski(sK2(X0,X1),X2) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_19911,plain,
% 15.37/2.50      ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 15.37/2.50      | r2_hidden(sK1(X0,X1),sK7)
% 15.37/2.50      | ~ r1_tarski(sK2(X0,X1),sK7) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_4308]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_54459,plain,
% 15.37/2.50      ( ~ r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7)
% 15.37/2.50      | ~ r1_tarski(sK2(X0,sK7),sK7) ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_19911]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_54460,plain,
% 15.37/2.50      ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) != iProver_top
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7) = iProver_top
% 15.37/2.50      | r1_tarski(sK2(X0,sK7),sK7) != iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_54459]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_54462,plain,
% 15.37/2.50      ( r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) != iProver_top
% 15.37/2.50      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top
% 15.37/2.50      | r1_tarski(sK2(sK6,sK7),sK7) != iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_54460]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_8,plain,
% 15.37/2.50      ( r2_hidden(sK1(X0,X1),X1)
% 15.37/2.50      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 15.37/2.50      | k3_tarski(X0) = X1 ),
% 15.37/2.50      inference(cnf_transformation,[],[f73]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_7155,plain,
% 15.37/2.50      ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7)
% 15.37/2.50      | k3_tarski(X0) = sK7 ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_8]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_7157,plain,
% 15.37/2.50      ( k3_tarski(X0) = sK7
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
% 15.37/2.50      inference(predicate_to_equality,[status(thm)],[c_7155]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(c_7159,plain,
% 15.37/2.50      ( k3_tarski(sK6) = sK7
% 15.37/2.50      | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) = iProver_top
% 15.37/2.50      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
% 15.37/2.50      inference(instantiation,[status(thm)],[c_7157]) ).
% 15.37/2.50  
% 15.37/2.50  cnf(contradiction,plain,
% 15.37/2.50      ( $false ),
% 15.37/2.50      inference(minisat,
% 15.37/2.50                [status(thm)],
% 15.37/2.50                [c_58210,c_54462,c_52189,c_51137,c_27730,c_10943,c_7159,
% 15.37/2.50                 c_2641,c_2610,c_2429,c_526,c_95,c_88,c_84,c_73,c_64,
% 15.37/2.50                 c_46,c_43,c_42,c_38,c_37]) ).
% 15.37/2.50  
% 15.37/2.50  
% 15.37/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.37/2.50  
% 15.37/2.50  ------                               Statistics
% 15.37/2.50  
% 15.37/2.50  ------ General
% 15.37/2.50  
% 15.37/2.50  abstr_ref_over_cycles:                  0
% 15.37/2.50  abstr_ref_under_cycles:                 0
% 15.37/2.50  gc_basic_clause_elim:                   0
% 15.37/2.50  forced_gc_time:                         0
% 15.37/2.50  parsing_time:                           0.009
% 15.37/2.50  unif_index_cands_time:                  0.
% 15.37/2.50  unif_index_add_time:                    0.
% 15.37/2.50  orderings_time:                         0.
% 15.37/2.50  out_proof_time:                         0.021
% 15.37/2.50  total_time:                             1.774
% 15.37/2.50  num_of_symbols:                         47
% 15.37/2.50  num_of_terms:                           51591
% 15.37/2.50  
% 15.37/2.50  ------ Preprocessing
% 15.37/2.50  
% 15.37/2.50  num_of_splits:                          0
% 15.37/2.50  num_of_split_atoms:                     0
% 15.37/2.50  num_of_reused_defs:                     0
% 15.37/2.50  num_eq_ax_congr_red:                    42
% 15.37/2.50  num_of_sem_filtered_clauses:            1
% 15.37/2.50  num_of_subtypes:                        0
% 15.37/2.50  monotx_restored_types:                  0
% 15.37/2.50  sat_num_of_epr_types:                   0
% 15.37/2.50  sat_num_of_non_cyclic_types:            0
% 15.37/2.50  sat_guarded_non_collapsed_types:        0
% 15.37/2.50  num_pure_diseq_elim:                    0
% 15.37/2.50  simp_replaced_by:                       0
% 15.37/2.50  res_preprocessed:                       161
% 15.37/2.50  prep_upred:                             0
% 15.37/2.50  prep_unflattend:                        8
% 15.37/2.50  smt_new_axioms:                         0
% 15.37/2.50  pred_elim_cands:                        5
% 15.37/2.50  pred_elim:                              0
% 15.37/2.50  pred_elim_cl:                           0
% 15.37/2.50  pred_elim_cycles:                       2
% 15.37/2.50  merged_defs:                            8
% 15.37/2.50  merged_defs_ncl:                        0
% 15.37/2.50  bin_hyper_res:                          8
% 15.37/2.50  prep_cycles:                            4
% 15.37/2.50  pred_elim_time:                         0.004
% 15.37/2.50  splitting_time:                         0.
% 15.37/2.50  sem_filter_time:                        0.
% 15.37/2.50  monotx_time:                            0.001
% 15.37/2.50  subtype_inf_time:                       0.
% 15.37/2.50  
% 15.37/2.50  ------ Problem properties
% 15.37/2.50  
% 15.37/2.50  clauses:                                36
% 15.37/2.50  conjectures:                            5
% 15.37/2.50  epr:                                    12
% 15.37/2.50  horn:                                   27
% 15.37/2.50  ground:                                 4
% 15.37/2.50  unary:                                  6
% 15.37/2.50  binary:                                 14
% 15.37/2.50  lits:                                   91
% 15.37/2.50  lits_eq:                                9
% 15.37/2.50  fd_pure:                                0
% 15.37/2.50  fd_pseudo:                              0
% 15.37/2.50  fd_cond:                                0
% 15.37/2.50  fd_pseudo_cond:                         6
% 15.37/2.50  ac_symbols:                             0
% 15.37/2.50  
% 15.37/2.50  ------ Propositional Solver
% 15.37/2.50  
% 15.37/2.50  prop_solver_calls:                      33
% 15.37/2.50  prop_fast_solver_calls:                 3668
% 15.37/2.50  smt_solver_calls:                       0
% 15.37/2.50  smt_fast_solver_calls:                  0
% 15.37/2.50  prop_num_of_clauses:                    24121
% 15.37/2.50  prop_preprocess_simplified:             52940
% 15.37/2.50  prop_fo_subsumed:                       686
% 15.37/2.50  prop_solver_time:                       0.
% 15.37/2.50  smt_solver_time:                        0.
% 15.37/2.50  smt_fast_solver_time:                   0.
% 15.37/2.50  prop_fast_solver_time:                  0.
% 15.37/2.50  prop_unsat_core_time:                   0.002
% 15.37/2.50  
% 15.37/2.50  ------ QBF
% 15.37/2.50  
% 15.37/2.50  qbf_q_res:                              0
% 15.37/2.50  qbf_num_tautologies:                    0
% 15.37/2.50  qbf_prep_cycles:                        0
% 15.37/2.50  
% 15.37/2.50  ------ BMC1
% 15.37/2.50  
% 15.37/2.50  bmc1_current_bound:                     -1
% 15.37/2.50  bmc1_last_solved_bound:                 -1
% 15.37/2.50  bmc1_unsat_core_size:                   -1
% 15.37/2.50  bmc1_unsat_core_parents_size:           -1
% 15.37/2.50  bmc1_merge_next_fun:                    0
% 15.37/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.37/2.50  
% 15.37/2.50  ------ Instantiation
% 15.37/2.50  
% 15.37/2.50  inst_num_of_clauses:                    5800
% 15.37/2.50  inst_num_in_passive:                    3146
% 15.37/2.50  inst_num_in_active:                     1949
% 15.37/2.50  inst_num_in_unprocessed:                705
% 15.37/2.50  inst_num_of_loops:                      2500
% 15.37/2.50  inst_num_of_learning_restarts:          0
% 15.37/2.50  inst_num_moves_active_passive:          549
% 15.37/2.50  inst_lit_activity:                      0
% 15.37/2.50  inst_lit_activity_moves:                0
% 15.37/2.50  inst_num_tautologies:                   0
% 15.37/2.50  inst_num_prop_implied:                  0
% 15.37/2.50  inst_num_existing_simplified:           0
% 15.37/2.50  inst_num_eq_res_simplified:             0
% 15.37/2.50  inst_num_child_elim:                    0
% 15.37/2.50  inst_num_of_dismatching_blockings:      6321
% 15.37/2.50  inst_num_of_non_proper_insts:           4843
% 15.37/2.50  inst_num_of_duplicates:                 0
% 15.37/2.50  inst_inst_num_from_inst_to_res:         0
% 15.37/2.50  inst_dismatching_checking_time:         0.
% 15.37/2.50  
% 15.37/2.50  ------ Resolution
% 15.37/2.50  
% 15.37/2.50  res_num_of_clauses:                     0
% 15.37/2.50  res_num_in_passive:                     0
% 15.37/2.50  res_num_in_active:                      0
% 15.37/2.50  res_num_of_loops:                       165
% 15.37/2.50  res_forward_subset_subsumed:            161
% 15.37/2.50  res_backward_subset_subsumed:           8
% 15.37/2.50  res_forward_subsumed:                   0
% 15.37/2.50  res_backward_subsumed:                  0
% 15.37/2.50  res_forward_subsumption_resolution:     0
% 15.37/2.50  res_backward_subsumption_resolution:    0
% 15.37/2.50  res_clause_to_clause_subsumption:       24799
% 15.37/2.50  res_orphan_elimination:                 0
% 15.37/2.50  res_tautology_del:                      501
% 15.37/2.50  res_num_eq_res_simplified:              0
% 15.37/2.50  res_num_sel_changes:                    0
% 15.37/2.50  res_moves_from_active_to_pass:          0
% 15.37/2.50  
% 15.37/2.50  ------ Superposition
% 15.37/2.50  
% 15.37/2.50  sup_time_total:                         0.
% 15.37/2.50  sup_time_generating:                    0.
% 15.37/2.50  sup_time_sim_full:                      0.
% 15.37/2.50  sup_time_sim_immed:                     0.
% 15.37/2.50  
% 15.37/2.50  sup_num_of_clauses:                     3329
% 15.37/2.50  sup_num_in_active:                      431
% 15.37/2.50  sup_num_in_passive:                     2898
% 15.37/2.50  sup_num_of_loops:                       499
% 15.37/2.50  sup_fw_superposition:                   1894
% 15.37/2.50  sup_bw_superposition:                   3398
% 15.37/2.50  sup_immediate_simplified:               1144
% 15.37/2.50  sup_given_eliminated:                   0
% 15.37/2.50  comparisons_done:                       0
% 15.37/2.50  comparisons_avoided:                    34
% 15.37/2.50  
% 15.37/2.50  ------ Simplifications
% 15.37/2.50  
% 15.37/2.50  
% 15.37/2.50  sim_fw_subset_subsumed:                 665
% 15.37/2.50  sim_bw_subset_subsumed:                 110
% 15.37/2.50  sim_fw_subsumed:                        291
% 15.37/2.50  sim_bw_subsumed:                        58
% 15.37/2.50  sim_fw_subsumption_res:                 0
% 15.37/2.50  sim_bw_subsumption_res:                 0
% 15.37/2.50  sim_tautology_del:                      90
% 15.37/2.50  sim_eq_tautology_del:                   82
% 15.37/2.50  sim_eq_res_simp:                        1
% 15.37/2.50  sim_fw_demodulated:                     40
% 15.37/2.50  sim_bw_demodulated:                     21
% 15.37/2.50  sim_light_normalised:                   201
% 15.37/2.50  sim_joinable_taut:                      0
% 15.37/2.50  sim_joinable_simp:                      0
% 15.37/2.50  sim_ac_normalised:                      0
% 15.37/2.50  sim_smt_subsumption:                    0
% 15.37/2.50  
%------------------------------------------------------------------------------
