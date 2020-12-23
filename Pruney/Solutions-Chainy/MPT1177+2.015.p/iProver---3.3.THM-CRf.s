%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:49 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  208 (4428 expanded)
%              Number of clauses        :  133 ( 815 expanded)
%              Number of leaves         :   19 (1446 expanded)
%              Depth                    :   27
%              Number of atoms          : 1021 (42677 expanded)
%              Number of equality atoms :  228 (1014 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f56])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_orders_2(X2,X0,X3)
            | ~ r2_xboole_0(X2,X3) )
          & ( m1_orders_2(X2,X0,X3)
            | r2_xboole_0(X2,X3) )
          & m2_orders_2(X3,X0,X1) )
     => ( ( ~ m1_orders_2(X2,X0,sK4)
          | ~ r2_xboole_0(X2,sK4) )
        & ( m1_orders_2(X2,X0,sK4)
          | r2_xboole_0(X2,sK4) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,X0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,X0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,X0,X1) )
          & m2_orders_2(X2,X0,X1) )
     => ( ? [X3] :
            ( ( ~ m1_orders_2(sK3,X0,X3)
              | ~ r2_xboole_0(sK3,X3) )
            & ( m1_orders_2(sK3,X0,X3)
              | r2_xboole_0(sK3,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,X0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,X0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,X0,sK2) )
            & m2_orders_2(X2,X0,sK2) )
        & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK1,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK1,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK1,X1) )
              & m2_orders_2(X2,sK1,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ m1_orders_2(sK3,sK1,sK4)
      | ~ r2_xboole_0(sK3,sK4) )
    & ( m1_orders_2(sK3,sK1,sK4)
      | r2_xboole_0(sK3,sK4) )
    & m2_orders_2(sK4,sK1,sK2)
    & m2_orders_2(sK3,sK1,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f60,f64,f63,f62,f61])).

fof(f104,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f101,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f99,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_2(X3,X0,X2)
      | ~ m1_orders_2(X2,X0,X3)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2096,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2098,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4435,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_2098])).

cnf(c_22,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2087,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2090,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3619,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2090])).

cnf(c_6052,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4435,c_3619])).

cnf(c_5700,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4435,c_2098])).

cnf(c_6053,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5700,c_3619])).

cnf(c_6057,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6052,c_6053])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2095,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8865,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6057,c_2095])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_31,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_301,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_302,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_546,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_302])).

cnf(c_547,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_2082,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_536,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_302])).

cnf(c_537,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_538,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_548,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2752,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3512,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2752])).

cnf(c_3513,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3512])).

cnf(c_33,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2085,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2086,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_34,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_723,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_724,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_891,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_724,c_35])).

cnf(c_892,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_38,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_36,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_896,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_39,c_38,c_37,c_36])).

cnf(c_1080,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X1,sK1,X0)
    | m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_896])).

cnf(c_2077,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_3356,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_2077])).

cnf(c_3805,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_3356])).

cnf(c_46,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_47,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2753,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_3622,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_3623,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3622])).

cnf(c_3814,plain,
    ( m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3805,c_46,c_47,c_548,c_3623])).

cnf(c_24,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_795,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_796,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_846,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_796,c_35])).

cnf(c_847,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_851,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_39,c_38,c_37,c_36])).

cnf(c_1088,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_851])).

cnf(c_2075,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_25,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_975,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_976,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_978,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_39,c_38,c_37,c_36])).

cnf(c_2080,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_2387,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_2080])).

cnf(c_2439,plain,
    ( m1_orders_2(X0,sK1,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2387])).

cnf(c_3820,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_2439])).

cnf(c_4835,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_538,c_548,c_3513,c_3820])).

cnf(c_29,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_2(X3,X1,X0)
    | ~ m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_684,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_2(X3,X1,X0)
    | ~ m1_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_685,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_921,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_685,c_35])).

cnf(c_922,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_926,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_39,c_38,c_37,c_36])).

cnf(c_1076,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_orders_2(X0,sK1,X1)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_926])).

cnf(c_2078,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_112,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_980,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_23,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_992,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_993,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_995,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_39,c_38,c_37,c_36])).

cnf(c_2079,plain,
    ( m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_2386,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_2079])).

cnf(c_4232,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2078,c_112,c_980,c_2386,c_2387])).

cnf(c_4233,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4232])).

cnf(c_4240,plain,
    ( sK4 = X0
    | m1_orders_2(X0,sK1,sK4) != iProver_top
    | m1_orders_2(sK4,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_4233])).

cnf(c_4847,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4835,c_4240])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_299,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_300,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_523,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_300])).

cnf(c_524,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_525,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_2303,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_2304,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_2319,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_2320,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2319])).

cnf(c_5301,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4847,c_47,c_525,c_538,c_548,c_2304,c_2320,c_3513,c_3820])).

cnf(c_5311,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5301,c_3814])).

cnf(c_26,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_23])).

cnf(c_215,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_951,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_35])).

cnf(c_952,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_956,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_39,c_38,c_37,c_36])).

cnf(c_957,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_956])).

cnf(c_2081,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_957])).

cnf(c_2385,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_2081])).

cnf(c_4815,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2385])).

cnf(c_5549,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5311,c_4815])).

cnf(c_5555,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5549,c_5311])).

cnf(c_27,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_762,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_763,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_867,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_763,c_35])).

cnf(c_868,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_872,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_39,c_38,c_37,c_36])).

cnf(c_1084,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_872])).

cnf(c_2076,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_2613,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2076])).

cnf(c_3175,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_2613])).

cnf(c_6357,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5555,c_3175])).

cnf(c_9024,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8865,c_6357])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.00  
% 3.01/1.00  ------  iProver source info
% 3.01/1.00  
% 3.01/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.00  git: non_committed_changes: false
% 3.01/1.00  git: last_make_outside_of_git: false
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     num_symb
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       true
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  ------ Parsing...
% 3.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.00  ------ Proving...
% 3.01/1.00  ------ Problem Properties 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  clauses                                 29
% 3.01/1.00  conjectures                             2
% 3.01/1.00  EPR                                     13
% 3.01/1.00  Horn                                    26
% 3.01/1.00  unary                                   5
% 3.01/1.00  binary                                  12
% 3.01/1.00  lits                                    70
% 3.01/1.00  lits eq                                 14
% 3.01/1.00  fd_pure                                 0
% 3.01/1.00  fd_pseudo                               0
% 3.01/1.00  fd_cond                                 4
% 3.01/1.00  fd_pseudo_cond                          3
% 3.01/1.00  AC symbols                              0
% 3.01/1.00  
% 3.01/1.00  ------ Schedule dynamic 5 is on 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  Current options:
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     none
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       false
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00   Resolution empty clause
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f76,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.01/1.00    inference(ennf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  fof(f74,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f15,axiom,(
% 3.01/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f35,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.01/1.00    inference(ennf_transformation,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f56,plain,(
% 3.01/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f57,plain,(
% 3.01/1.00    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f56])).
% 3.01/1.00  
% 3.01/1.00  fof(f86,plain,(
% 3.01/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f57])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,axiom,(
% 3.01/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f85,plain,(
% 3.01/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f8,axiom,(
% 3.01/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.01/1.00    inference(nnf_transformation,[],[f8])).
% 3.01/1.00  
% 3.01/1.00  fof(f78,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f1,axiom,(
% 3.01/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.01/1.00    inference(nnf_transformation,[],[f1])).
% 3.01/1.00  
% 3.01/1.00  fof(f51,plain,(
% 3.01/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.01/1.00    inference(flattening,[],[f50])).
% 3.01/1.00  
% 3.01/1.00  fof(f67,plain,(
% 3.01/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f51])).
% 3.01/1.00  
% 3.01/1.00  fof(f106,plain,(
% 3.01/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 3.01/1.00    inference(equality_resolution,[],[f67])).
% 3.01/1.00  
% 3.01/1.00  fof(f22,conjecture,(
% 3.01/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f23,negated_conjecture,(
% 3.01/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 3.01/1.00    inference(negated_conjecture,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f59,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f49])).
% 3.01/1.00  
% 3.01/1.00  fof(f60,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f59])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f63,plain,(
% 3.01/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f61,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f65,plain,(
% 3.01/1.00    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f60,f64,f63,f62,f61])).
% 3.01/1.00  
% 3.01/1.00  fof(f104,plain,(
% 3.01/1.00    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f51])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/1.00    inference(nnf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/1.00    inference(flattening,[],[f52])).
% 3.01/1.00  
% 3.01/1.00  fof(f73,plain,(
% 3.01/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f53])).
% 3.01/1.00  
% 3.01/1.00  fof(f102,plain,(
% 3.01/1.00    m2_orders_2(sK3,sK1,sK2)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f103,plain,(
% 3.01/1.00    m2_orders_2(sK4,sK1,sK2)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f21,axiom,(
% 3.01/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f21])).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f46])).
% 3.01/1.00  
% 3.01/1.00  fof(f58,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f47])).
% 3.01/1.00  
% 3.01/1.00  fof(f95,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f101,plain,(
% 3.01/1.00    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f100,plain,(
% 3.01/1.00    l1_orders_2(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f96,plain,(
% 3.01/1.00    ~v2_struct_0(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f97,plain,(
% 3.01/1.00    v3_orders_2(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f98,plain,(
% 3.01/1.00    v4_orders_2(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f99,plain,(
% 3.01/1.00    v5_orders_2(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f17,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    inference(pure_predicate_removal,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f38])).
% 3.01/1.00  
% 3.01/1.00  fof(f90,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f39])).
% 3.01/1.00  
% 3.01/1.00  fof(f18,axiom,(
% 3.01/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f40])).
% 3.01/1.00  
% 3.01/1.00  fof(f91,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f41])).
% 3.01/1.00  
% 3.01/1.00  fof(f94,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f16,axiom,(
% 3.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f89,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f68,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f51])).
% 3.01/1.00  
% 3.01/1.00  fof(f105,plain,(
% 3.01/1.00    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f65])).
% 3.01/1.00  
% 3.01/1.00  fof(f19,axiom,(
% 3.01/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f42])).
% 3.01/1.00  
% 3.01/1.00  fof(f92,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f43])).
% 3.01/1.00  
% 3.01/1.00  fof(f20,axiom,(
% 3.01/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f20])).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f44])).
% 3.01/1.00  
% 3.01/1.00  fof(f93,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  cnf(c_10,plain,
% 3.01/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2096,plain,
% 3.01/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_8,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2098,plain,
% 3.01/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 3.01/1.00      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4435,plain,
% 3.01/1.00      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2096,c_2098]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_22,plain,
% 3.01/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2087,plain,
% 3.01/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_19,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2090,plain,
% 3.01/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3619,plain,
% 3.01/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,sK0(X0)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2087,c_2090]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6052,plain,
% 3.01/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4435,c_3619]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5700,plain,
% 3.01/1.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4435,c_2098]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6053,plain,
% 3.01/1.00      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_5700,c_3619]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6057,plain,
% 3.01/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_6052,c_6053]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_11,plain,
% 3.01/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2095,plain,
% 3.01/1.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_8865,plain,
% 3.01/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_6057,c_2095]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_31,negated_conjecture,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_301,plain,
% 3.01/1.00      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 3.01/1.00      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_302,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_301]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_546,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_302]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_547,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_546]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2082,plain,
% 3.01/1.00      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2,plain,
% 3.01/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_536,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(X0,X1) | sK4 != X1 | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_302]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_537,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_538,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 3.01/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_548,plain,
% 3.01/1.00      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2752,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3512,plain,
% 3.01/1.00      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2752]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3513,plain,
% 3.01/1.00      ( sK3 = sK4
% 3.01/1.00      | r1_tarski(sK4,sK3) != iProver_top
% 3.01/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3512]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_33,negated_conjecture,
% 3.01/1.00      ( m2_orders_2(sK3,sK1,sK2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2085,plain,
% 3.01/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_32,negated_conjecture,
% 3.01/1.00      ( m2_orders_2(sK4,sK1,sK2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2086,plain,
% 3.01/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_28,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | m1_orders_2(X3,X1,X0)
% 3.01/1.00      | m1_orders_2(X0,X1,X3)
% 3.01/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X3 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_34,negated_conjecture,
% 3.01/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 3.01/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_723,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | m1_orders_2(X3,X1,X0)
% 3.01/1.00      | m1_orders_2(X0,X1,X3)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X3 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK2 != X2 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_724,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | m1_orders_2(X0,X1,X2)
% 3.01/1.00      | m1_orders_2(X2,X1,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X0 = X2
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_35,negated_conjecture,
% 3.01/1.00      ( l1_orders_2(sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_891,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | m1_orders_2(X0,X1,X2)
% 3.01/1.00      | m1_orders_2(X2,X1,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | X2 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_724,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_892,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1)
% 3.01/1.00      | X1 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_891]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_39,negated_conjecture,
% 3.01/1.00      ( ~ v2_struct_0(sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_38,negated_conjecture,
% 3.01/1.00      ( v3_orders_2(sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_37,negated_conjecture,
% 3.01/1.00      ( v4_orders_2(sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_36,negated_conjecture,
% 3.01/1.00      ( v5_orders_2(sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_896,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | X1 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_892,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1080,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | X1 = X0 ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_896]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2077,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3356,plain,
% 3.01/1.00      ( sK4 = X0
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 3.01/1.00      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2086,c_2077]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3805,plain,
% 3.01/1.00      ( sK4 = sK3
% 3.01/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 3.01/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2085,c_3356]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_46,plain,
% 3.01/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_47,plain,
% 3.01/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2753,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 3.01/1.00      | m1_orders_2(X0,sK1,sK4)
% 3.01/1.00      | m1_orders_2(sK4,sK1,X0)
% 3.01/1.00      | X0 = sK4 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3622,plain,
% 3.01/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 3.01/1.00      | m1_orders_2(sK4,sK1,sK3)
% 3.01/1.00      | m1_orders_2(sK3,sK1,sK4)
% 3.01/1.00      | sK3 = sK4 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2753]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3623,plain,
% 3.01/1.00      ( sK3 = sK4
% 3.01/1.00      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 3.01/1.00      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 3.01/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3622]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3814,plain,
% 3.01/1.00      ( m1_orders_2(sK4,sK1,sK3) = iProver_top
% 3.01/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3805,c_46,c_47,c_548,c_3623]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_24,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_795,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK2 != X2 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_796,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_795]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_846,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_796,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_847,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_846]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_851,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_847,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1088,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_851]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2075,plain,
% 3.01/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_25,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | r1_tarski(X0,X2)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_975,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | r1_tarski(X0,X2)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_976,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | r1_tarski(X0,X1)
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_975]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_978,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | r1_tarski(X0,X1) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_976,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2080,plain,
% 3.01/1.00      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.01/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2387,plain,
% 3.01/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.01/1.00      | r1_tarski(X1,X0) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2075,c_2080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2439,plain,
% 3.01/1.00      ( m1_orders_2(X0,sK1,sK3) != iProver_top
% 3.01/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2085,c_2387]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3820,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 3.01/1.00      | r1_tarski(sK4,sK3) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3814,c_2439]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4835,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2082,c_538,c_548,c_3513,c_3820]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_29,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X3,X1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,X1,X3)
% 3.01/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X3 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_684,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X3,X1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,X1,X3)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X3 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK2 != X2 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_685,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | X0 = X2
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_684]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_921,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | X2 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_685,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_922,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1)
% 3.01/1.00      | X1 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_921]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_926,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | X1 = X0
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_922,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1076,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | X1 = X0 ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_926]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2078,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_112,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.01/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_980,plain,
% 3.01/1.00      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.01/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_23,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_992,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_993,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_992]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_995,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_993,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2079,plain,
% 3.01/1.00      ( m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2386,plain,
% 3.01/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.01/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2075,c_2079]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4232,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2078,c_112,c_980,c_2386,c_2387]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4233,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_4232]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4240,plain,
% 3.01/1.00      ( sK4 = X0
% 3.01/1.00      | m1_orders_2(X0,sK1,sK4) != iProver_top
% 3.01/1.00      | m1_orders_2(sK4,sK1,X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2086,c_4233]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4847,plain,
% 3.01/1.00      ( sK4 = sK3 | m1_orders_2(sK4,sK1,sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4835,c_4240]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_0,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_30,negated_conjecture,
% 3.01/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 3.01/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_299,plain,
% 3.01/1.00      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 3.01/1.00      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_300,plain,
% 3.01/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_299]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_523,plain,
% 3.01/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 3.01/1.00      | ~ r1_tarski(X0,X1)
% 3.01/1.00      | X1 = X0
% 3.01/1.00      | sK4 != X1
% 3.01/1.00      | sK3 != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_300]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_524,plain,
% 3.01/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_523]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_525,plain,
% 3.01/1.00      ( sK4 = sK3
% 3.01/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 3.01/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2303,plain,
% 3.01/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 3.01/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2304,plain,
% 3.01/1.00      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2319,plain,
% 3.01/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 3.01/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | r1_tarski(sK3,sK4) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_978]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2320,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 3.01/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.01/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2319]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5301,plain,
% 3.01/1.00      ( sK4 = sK3 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4847,c_47,c_525,c_538,c_548,c_2304,c_2320,c_3513,c_3820]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5311,plain,
% 3.01/1.00      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_5301,c_3814]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_26,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_xboole_0 = X2 ),
% 3.01/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_214,plain,
% 3.01/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_xboole_0 = X2 ),
% 3.01/1.00      inference(global_propositional_subsumption,[status(thm)],[c_26,c_23]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_215,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_xboole_0 = X2 ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_214]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_951,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.01/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | sK1 != X1
% 3.01/1.00      | k1_xboole_0 = X2 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_215,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_952,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1)
% 3.01/1.00      | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_951]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_956,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | k1_xboole_0 = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_952,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_957,plain,
% 3.01/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 3.01/1.00      | ~ m1_orders_2(X1,sK1,X0)
% 3.01/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.01/1.00      | k1_xboole_0 = X1 ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_956]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2081,plain,
% 3.01/1.00      ( k1_xboole_0 = X0
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_957]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2385,plain,
% 3.01/1.00      ( k1_xboole_0 = X0
% 3.01/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.01/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2075,c_2081]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4815,plain,
% 3.01/1.00      ( sK3 = k1_xboole_0
% 3.01/1.00      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 3.01/1.00      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2085,c_2385]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5549,plain,
% 3.01/1.00      ( sK3 = k1_xboole_0 | m1_orders_2(sK3,sK1,sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_5311,c_4815]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5555,plain,
% 3.01/1.00      ( sK3 = k1_xboole_0 ),
% 3.01/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5549,c_5311]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_27,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ r1_xboole_0(X0,X3)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_762,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.01/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.01/1.00      | ~ r1_xboole_0(X0,X3)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK2 != X2 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_763,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | ~ r1_xboole_0(X2,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | ~ l1_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_762]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_867,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 3.01/1.00      | ~ r1_xboole_0(X2,X0)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v3_orders_2(X1)
% 3.01/1.00      | ~ v4_orders_2(X1)
% 3.01/1.00      | ~ v5_orders_2(X1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 3.01/1.00      | sK1 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_763,c_35]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_868,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ r1_xboole_0(X1,X0)
% 3.01/1.00      | v2_struct_0(sK1)
% 3.01/1.00      | ~ v3_orders_2(sK1)
% 3.01/1.00      | ~ v4_orders_2(sK1)
% 3.01/1.00      | ~ v5_orders_2(sK1)
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_867]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_872,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ r1_xboole_0(X1,X0)
% 3.01/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_868,c_39,c_38,c_37,c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1084,plain,
% 3.01/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.01/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 3.01/1.00      | ~ r1_xboole_0(X1,X0) ),
% 3.01/1.00      inference(equality_resolution_simp,[status(thm)],[c_872]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2076,plain,
% 3.01/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.01/1.00      | r1_xboole_0(X1,X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2613,plain,
% 3.01/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.01/1.00      | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2085,c_2076]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3175,plain,
% 3.01/1.00      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2085,c_2613]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6357,plain,
% 3.01/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_5555,c_3175]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_9024,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_8865,c_6357]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.009
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.011
% 3.01/1.00  total_time:                             0.243
% 3.01/1.00  num_of_symbols:                         58
% 3.01/1.00  num_of_terms:                           8646
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          0
% 3.01/1.00  num_of_split_atoms:                     0
% 3.01/1.00  num_of_reused_defs:                     0
% 3.01/1.00  num_eq_ax_congr_red:                    34
% 3.01/1.00  num_of_sem_filtered_clauses:            1
% 3.01/1.00  num_of_subtypes:                        0
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        0
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       146
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        51
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        6
% 3.01/1.00  pred_elim:                              8
% 3.01/1.00  pred_elim_cl:                           9
% 3.01/1.00  pred_elim_cycles:                       11
% 3.01/1.00  merged_defs:                            18
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          19
% 3.01/1.00  prep_cycles:                            4
% 3.01/1.00  pred_elim_time:                         0.014
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                29
% 3.01/1.00  conjectures:                            2
% 3.01/1.00  epr:                                    13
% 3.01/1.00  horn:                                   26
% 3.01/1.00  ground:                                 5
% 3.01/1.00  unary:                                  5
% 3.01/1.00  binary:                                 12
% 3.01/1.00  lits:                                   70
% 3.01/1.00  lits_eq:                                14
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                4
% 3.01/1.00  fd_pseudo_cond:                         3
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      28
% 3.01/1.00  prop_fast_solver_calls:                 1210
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    3514
% 3.01/1.00  prop_preprocess_simplified:             9655
% 3.01/1.00  prop_fo_subsumed:                       37
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    927
% 3.01/1.00  inst_num_in_passive:                    277
% 3.01/1.00  inst_num_in_active:                     445
% 3.01/1.00  inst_num_in_unprocessed:                205
% 3.01/1.00  inst_num_of_loops:                      480
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          33
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      295
% 3.01/1.00  inst_num_of_non_proper_insts:           876
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       150
% 3.01/1.00  res_forward_subset_subsumed:            55
% 3.01/1.00  res_backward_subset_subsumed:           0
% 3.01/1.00  res_forward_subsumed:                   0
% 3.01/1.00  res_backward_subsumed:                  0
% 3.01/1.00  res_forward_subsumption_resolution:     0
% 3.01/1.00  res_backward_subsumption_resolution:    0
% 3.01/1.00  res_clause_to_clause_subsumption:       467
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      78
% 3.01/1.00  res_num_eq_res_simplified:              4
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     97
% 3.01/1.00  sup_num_in_active:                      61
% 3.01/1.00  sup_num_in_passive:                     36
% 3.01/1.00  sup_num_of_loops:                       95
% 3.01/1.00  sup_fw_superposition:                   61
% 3.01/1.00  sup_bw_superposition:                   86
% 3.01/1.00  sup_immediate_simplified:               19
% 3.01/1.00  sup_given_eliminated:                   3
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    0
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 9
% 3.01/1.00  sim_bw_subset_subsumed:                 10
% 3.01/1.00  sim_fw_subsumed:                        9
% 3.01/1.00  sim_bw_subsumed:                        0
% 3.01/1.00  sim_fw_subsumption_res:                 1
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      2
% 3.01/1.00  sim_eq_tautology_del:                   12
% 3.01/1.00  sim_eq_res_simp:                        0
% 3.01/1.00  sim_fw_demodulated:                     1
% 3.01/1.00  sim_bw_demodulated:                     35
% 3.01/1.00  sim_light_normalised:                   4
% 3.01/1.00  sim_joinable_taut:                      0
% 3.01/1.00  sim_joinable_simp:                      0
% 3.01/1.00  sim_ac_normalised:                      0
% 3.01/1.00  sim_smt_subsumption:                    0
% 3.01/1.00  
%------------------------------------------------------------------------------
