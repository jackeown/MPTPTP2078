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
% DateTime   : Thu Dec  3 12:13:04 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 345 expanded)
%              Number of clauses        :   63 (  91 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  509 (1923 expanded)
%              Number of equality atoms :  119 ( 345 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK6))
        & m1_orders_1(sK6,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK5))) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6))
    & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f40,f39])).

fof(f63,plain,(
    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK4(X0),X0)
        & k1_xboole_0 != sK4(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK4(X0),X0)
          & k1_xboole_0 != sK4(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f37])).

fof(f55,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_507,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,X1))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_508,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK6))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_685,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK6))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_508,c_18])).

cnf(c_686,plain,
    ( v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_xboole_0(k4_orders_2(sK5,sK6))
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_688,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK5,sK6))
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_22,c_21,c_20,c_19])).

cnf(c_866,plain,
    ( r2_hidden(sK0(X0),X0)
    | k4_orders_2(sK5,sK6) != X0
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_688])).

cnf(c_867,plain,
    ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_866])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1409,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2364,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1409])).

cnf(c_2438,plain,
    ( sK0(k4_orders_2(sK5,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1406,c_2364])).

cnf(c_5,plain,
    ( r1_xboole_0(k3_tarski(X0),X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1411,plain,
    ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_873,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_874,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_1407,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_1909,plain,
    ( r1_xboole_0(k3_tarski(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1407])).

cnf(c_3,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1917,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1909,c_3])).

cnf(c_1921,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_1043,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1778,plain,
    ( X0 != X1
    | X0 = sK0(k4_orders_2(sK5,sK6))
    | sK0(k4_orders_2(sK5,sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1779,plain,
    ( sK0(k4_orders_2(sK5,sK6)) != k1_xboole_0
    | k1_xboole_0 = sK0(k4_orders_2(sK5,sK6))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1778])).

cnf(c_1042,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1637,plain,
    ( k4_orders_2(sK5,sK6) = k4_orders_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_1045,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1539,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6))
    | X1 != k4_orders_2(sK5,sK6)
    | X0 != sK0(k4_orders_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1636,plain,
    ( r2_hidden(X0,k4_orders_2(sK5,sK6))
    | ~ r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6))
    | X0 != sK0(k4_orders_2(sK5,sK6))
    | k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_1638,plain,
    ( X0 != sK0(k4_orders_2(sK5,sK6))
    | k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6)
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) = iProver_top
    | r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_1640,plain,
    ( k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6)
    | k1_xboole_0 != sK0(k4_orders_2(sK5,sK6))
    | r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) != iProver_top
    | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1061,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_9,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_447,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_448,plain,
    ( m2_orders_2(X0,X1,sK6)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_782,plain,
    ( m2_orders_2(X0,X1,sK6)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_448,c_18])).

cnf(c_783,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_787,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_22,c_21,c_20,c_19])).

cnf(c_915,plain,
    ( m2_orders_2(X0,sK5,sK6)
    | ~ r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
    inference(equality_resolution_simp,[status(thm)],[c_787])).

cnf(c_916,plain,
    ( m2_orders_2(X0,sK5,sK6) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_918,plain,
    ( m2_orders_2(k1_xboole_0,sK5,sK6) = iProver_top
    | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_414,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_415,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | ~ m2_orders_2(X2,X1,sK6)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_803,plain,
    ( ~ m2_orders_2(X0,X1,sK6)
    | ~ m2_orders_2(X2,X1,sK6)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_18])).

cnf(c_804,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_808,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1)
    | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_22,c_21,c_20,c_19])).

cnf(c_911,plain,
    ( ~ m2_orders_2(X0,sK5,sK6)
    | ~ m2_orders_2(X1,sK5,sK6)
    | ~ r1_xboole_0(X0,X1) ),
    inference(equality_resolution_simp,[status(thm)],[c_808])).

cnf(c_912,plain,
    ( m2_orders_2(X0,sK5,sK6) != iProver_top
    | m2_orders_2(X1,sK5,sK6) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_914,plain,
    ( m2_orders_2(k1_xboole_0,sK5,sK6) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_868,plain,
    ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2438,c_1921,c_1779,c_1637,c_1640,c_1061,c_918,c_914,c_868])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.58/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/1.00  
% 1.58/1.00  ------  iProver source info
% 1.58/1.00  
% 1.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/1.00  git: non_committed_changes: false
% 1.58/1.00  git: last_make_outside_of_git: false
% 1.58/1.00  
% 1.58/1.00  ------ 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options
% 1.58/1.00  
% 1.58/1.00  --out_options                           all
% 1.58/1.00  --tptp_safe_out                         true
% 1.58/1.00  --problem_path                          ""
% 1.58/1.00  --include_path                          ""
% 1.58/1.00  --clausifier                            res/vclausify_rel
% 1.58/1.00  --clausifier_options                    --mode clausify
% 1.58/1.00  --stdin                                 false
% 1.58/1.00  --stats_out                             all
% 1.58/1.00  
% 1.58/1.00  ------ General Options
% 1.58/1.00  
% 1.58/1.00  --fof                                   false
% 1.58/1.00  --time_out_real                         305.
% 1.58/1.00  --time_out_virtual                      -1.
% 1.58/1.00  --symbol_type_check                     false
% 1.58/1.00  --clausify_out                          false
% 1.58/1.00  --sig_cnt_out                           false
% 1.58/1.00  --trig_cnt_out                          false
% 1.58/1.00  --trig_cnt_out_tolerance                1.
% 1.58/1.00  --trig_cnt_out_sk_spl                   false
% 1.58/1.00  --abstr_cl_out                          false
% 1.58/1.00  
% 1.58/1.00  ------ Global Options
% 1.58/1.00  
% 1.58/1.00  --schedule                              default
% 1.58/1.00  --add_important_lit                     false
% 1.58/1.00  --prop_solver_per_cl                    1000
% 1.58/1.00  --min_unsat_core                        false
% 1.58/1.00  --soft_assumptions                      false
% 1.58/1.00  --soft_lemma_size                       3
% 1.58/1.00  --prop_impl_unit_size                   0
% 1.58/1.00  --prop_impl_unit                        []
% 1.58/1.00  --share_sel_clauses                     true
% 1.58/1.00  --reset_solvers                         false
% 1.58/1.00  --bc_imp_inh                            [conj_cone]
% 1.58/1.00  --conj_cone_tolerance                   3.
% 1.58/1.00  --extra_neg_conj                        none
% 1.58/1.00  --large_theory_mode                     true
% 1.58/1.00  --prolific_symb_bound                   200
% 1.58/1.00  --lt_threshold                          2000
% 1.58/1.00  --clause_weak_htbl                      true
% 1.58/1.00  --gc_record_bc_elim                     false
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing Options
% 1.58/1.00  
% 1.58/1.00  --preprocessing_flag                    true
% 1.58/1.00  --time_out_prep_mult                    0.1
% 1.58/1.00  --splitting_mode                        input
% 1.58/1.00  --splitting_grd                         true
% 1.58/1.00  --splitting_cvd                         false
% 1.58/1.00  --splitting_cvd_svl                     false
% 1.58/1.00  --splitting_nvd                         32
% 1.58/1.00  --sub_typing                            true
% 1.58/1.00  --prep_gs_sim                           true
% 1.58/1.00  --prep_unflatten                        true
% 1.58/1.00  --prep_res_sim                          true
% 1.58/1.00  --prep_upred                            true
% 1.58/1.00  --prep_sem_filter                       exhaustive
% 1.58/1.00  --prep_sem_filter_out                   false
% 1.58/1.00  --pred_elim                             true
% 1.58/1.00  --res_sim_input                         true
% 1.58/1.00  --eq_ax_congr_red                       true
% 1.58/1.00  --pure_diseq_elim                       true
% 1.58/1.00  --brand_transform                       false
% 1.58/1.00  --non_eq_to_eq                          false
% 1.58/1.00  --prep_def_merge                        true
% 1.58/1.00  --prep_def_merge_prop_impl              false
% 1.58/1.00  --prep_def_merge_mbd                    true
% 1.58/1.00  --prep_def_merge_tr_red                 false
% 1.58/1.00  --prep_def_merge_tr_cl                  false
% 1.58/1.00  --smt_preprocessing                     true
% 1.58/1.00  --smt_ac_axioms                         fast
% 1.58/1.00  --preprocessed_out                      false
% 1.58/1.00  --preprocessed_stats                    false
% 1.58/1.00  
% 1.58/1.00  ------ Abstraction refinement Options
% 1.58/1.00  
% 1.58/1.00  --abstr_ref                             []
% 1.58/1.00  --abstr_ref_prep                        false
% 1.58/1.00  --abstr_ref_until_sat                   false
% 1.58/1.00  --abstr_ref_sig_restrict                funpre
% 1.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.00  --abstr_ref_under                       []
% 1.58/1.00  
% 1.58/1.00  ------ SAT Options
% 1.58/1.00  
% 1.58/1.00  --sat_mode                              false
% 1.58/1.00  --sat_fm_restart_options                ""
% 1.58/1.00  --sat_gr_def                            false
% 1.58/1.00  --sat_epr_types                         true
% 1.58/1.00  --sat_non_cyclic_types                  false
% 1.58/1.00  --sat_finite_models                     false
% 1.58/1.00  --sat_fm_lemmas                         false
% 1.58/1.00  --sat_fm_prep                           false
% 1.58/1.00  --sat_fm_uc_incr                        true
% 1.58/1.00  --sat_out_model                         small
% 1.58/1.00  --sat_out_clauses                       false
% 1.58/1.00  
% 1.58/1.00  ------ QBF Options
% 1.58/1.00  
% 1.58/1.00  --qbf_mode                              false
% 1.58/1.00  --qbf_elim_univ                         false
% 1.58/1.00  --qbf_dom_inst                          none
% 1.58/1.00  --qbf_dom_pre_inst                      false
% 1.58/1.00  --qbf_sk_in                             false
% 1.58/1.00  --qbf_pred_elim                         true
% 1.58/1.00  --qbf_split                             512
% 1.58/1.00  
% 1.58/1.00  ------ BMC1 Options
% 1.58/1.00  
% 1.58/1.00  --bmc1_incremental                      false
% 1.58/1.00  --bmc1_axioms                           reachable_all
% 1.58/1.00  --bmc1_min_bound                        0
% 1.58/1.00  --bmc1_max_bound                        -1
% 1.58/1.00  --bmc1_max_bound_default                -1
% 1.58/1.00  --bmc1_symbol_reachability              true
% 1.58/1.00  --bmc1_property_lemmas                  false
% 1.58/1.00  --bmc1_k_induction                      false
% 1.58/1.00  --bmc1_non_equiv_states                 false
% 1.58/1.00  --bmc1_deadlock                         false
% 1.58/1.00  --bmc1_ucm                              false
% 1.58/1.00  --bmc1_add_unsat_core                   none
% 1.58/1.00  --bmc1_unsat_core_children              false
% 1.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.00  --bmc1_out_stat                         full
% 1.58/1.00  --bmc1_ground_init                      false
% 1.58/1.00  --bmc1_pre_inst_next_state              false
% 1.58/1.00  --bmc1_pre_inst_state                   false
% 1.58/1.00  --bmc1_pre_inst_reach_state             false
% 1.58/1.00  --bmc1_out_unsat_core                   false
% 1.58/1.00  --bmc1_aig_witness_out                  false
% 1.58/1.00  --bmc1_verbose                          false
% 1.58/1.00  --bmc1_dump_clauses_tptp                false
% 1.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.00  --bmc1_dump_file                        -
% 1.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.00  --bmc1_ucm_extend_mode                  1
% 1.58/1.00  --bmc1_ucm_init_mode                    2
% 1.58/1.00  --bmc1_ucm_cone_mode                    none
% 1.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.00  --bmc1_ucm_relax_model                  4
% 1.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.00  --bmc1_ucm_layered_model                none
% 1.58/1.00  --bmc1_ucm_max_lemma_size               10
% 1.58/1.00  
% 1.58/1.00  ------ AIG Options
% 1.58/1.00  
% 1.58/1.00  --aig_mode                              false
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation Options
% 1.58/1.00  
% 1.58/1.00  --instantiation_flag                    true
% 1.58/1.00  --inst_sos_flag                         false
% 1.58/1.00  --inst_sos_phase                        true
% 1.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel_side                     num_symb
% 1.58/1.00  --inst_solver_per_active                1400
% 1.58/1.00  --inst_solver_calls_frac                1.
% 1.58/1.00  --inst_passive_queue_type               priority_queues
% 1.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.00  --inst_passive_queues_freq              [25;2]
% 1.58/1.00  --inst_dismatching                      true
% 1.58/1.00  --inst_eager_unprocessed_to_passive     true
% 1.58/1.00  --inst_prop_sim_given                   true
% 1.58/1.00  --inst_prop_sim_new                     false
% 1.58/1.00  --inst_subs_new                         false
% 1.58/1.00  --inst_eq_res_simp                      false
% 1.58/1.00  --inst_subs_given                       false
% 1.58/1.00  --inst_orphan_elimination               true
% 1.58/1.00  --inst_learning_loop_flag               true
% 1.58/1.00  --inst_learning_start                   3000
% 1.58/1.00  --inst_learning_factor                  2
% 1.58/1.00  --inst_start_prop_sim_after_learn       3
% 1.58/1.00  --inst_sel_renew                        solver
% 1.58/1.00  --inst_lit_activity_flag                true
% 1.58/1.00  --inst_restr_to_given                   false
% 1.58/1.00  --inst_activity_threshold               500
% 1.58/1.00  --inst_out_proof                        true
% 1.58/1.00  
% 1.58/1.00  ------ Resolution Options
% 1.58/1.00  
% 1.58/1.00  --resolution_flag                       true
% 1.58/1.00  --res_lit_sel                           adaptive
% 1.58/1.00  --res_lit_sel_side                      none
% 1.58/1.00  --res_ordering                          kbo
% 1.58/1.00  --res_to_prop_solver                    active
% 1.58/1.00  --res_prop_simpl_new                    false
% 1.58/1.00  --res_prop_simpl_given                  true
% 1.58/1.00  --res_passive_queue_type                priority_queues
% 1.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.00  --res_passive_queues_freq               [15;5]
% 1.58/1.00  --res_forward_subs                      full
% 1.58/1.00  --res_backward_subs                     full
% 1.58/1.00  --res_forward_subs_resolution           true
% 1.58/1.00  --res_backward_subs_resolution          true
% 1.58/1.00  --res_orphan_elimination                true
% 1.58/1.00  --res_time_limit                        2.
% 1.58/1.00  --res_out_proof                         true
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Options
% 1.58/1.00  
% 1.58/1.00  --superposition_flag                    true
% 1.58/1.00  --sup_passive_queue_type                priority_queues
% 1.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.00  --demod_completeness_check              fast
% 1.58/1.00  --demod_use_ground                      true
% 1.58/1.00  --sup_to_prop_solver                    passive
% 1.58/1.00  --sup_prop_simpl_new                    true
% 1.58/1.00  --sup_prop_simpl_given                  true
% 1.58/1.00  --sup_fun_splitting                     false
% 1.58/1.00  --sup_smt_interval                      50000
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Simplification Setup
% 1.58/1.00  
% 1.58/1.00  --sup_indices_passive                   []
% 1.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_full_bw                           [BwDemod]
% 1.58/1.00  --sup_immed_triv                        [TrivRules]
% 1.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_immed_bw_main                     []
% 1.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  
% 1.58/1.00  ------ Combination Options
% 1.58/1.00  
% 1.58/1.00  --comb_res_mult                         3
% 1.58/1.00  --comb_sup_mult                         2
% 1.58/1.00  --comb_inst_mult                        10
% 1.58/1.00  
% 1.58/1.00  ------ Debug Options
% 1.58/1.00  
% 1.58/1.00  --dbg_backtrace                         false
% 1.58/1.00  --dbg_dump_prop_clauses                 false
% 1.58/1.00  --dbg_dump_prop_clauses_file            -
% 1.58/1.00  --dbg_out_stat                          false
% 1.58/1.00  ------ Parsing...
% 1.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.58/1.00  ------ Proving...
% 1.58/1.00  ------ Problem Properties 
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  clauses                                 17
% 1.58/1.00  conjectures                             1
% 1.58/1.00  EPR                                     2
% 1.58/1.00  Horn                                    14
% 1.58/1.00  unary                                   6
% 1.58/1.00  binary                                  7
% 1.58/1.00  lits                                    32
% 1.58/1.00  lits eq                                 10
% 1.58/1.00  fd_pure                                 0
% 1.58/1.00  fd_pseudo                               0
% 1.58/1.00  fd_cond                                 3
% 1.58/1.00  fd_pseudo_cond                          0
% 1.58/1.00  AC symbols                              0
% 1.58/1.00  
% 1.58/1.00  ------ Schedule dynamic 5 is on 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  ------ 
% 1.58/1.00  Current options:
% 1.58/1.00  ------ 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options
% 1.58/1.00  
% 1.58/1.00  --out_options                           all
% 1.58/1.00  --tptp_safe_out                         true
% 1.58/1.00  --problem_path                          ""
% 1.58/1.00  --include_path                          ""
% 1.58/1.00  --clausifier                            res/vclausify_rel
% 1.58/1.00  --clausifier_options                    --mode clausify
% 1.58/1.00  --stdin                                 false
% 1.58/1.00  --stats_out                             all
% 1.58/1.00  
% 1.58/1.00  ------ General Options
% 1.58/1.00  
% 1.58/1.00  --fof                                   false
% 1.58/1.00  --time_out_real                         305.
% 1.58/1.00  --time_out_virtual                      -1.
% 1.58/1.00  --symbol_type_check                     false
% 1.58/1.00  --clausify_out                          false
% 1.58/1.00  --sig_cnt_out                           false
% 1.58/1.00  --trig_cnt_out                          false
% 1.58/1.00  --trig_cnt_out_tolerance                1.
% 1.58/1.00  --trig_cnt_out_sk_spl                   false
% 1.58/1.00  --abstr_cl_out                          false
% 1.58/1.00  
% 1.58/1.00  ------ Global Options
% 1.58/1.00  
% 1.58/1.00  --schedule                              default
% 1.58/1.00  --add_important_lit                     false
% 1.58/1.00  --prop_solver_per_cl                    1000
% 1.58/1.00  --min_unsat_core                        false
% 1.58/1.00  --soft_assumptions                      false
% 1.58/1.00  --soft_lemma_size                       3
% 1.58/1.00  --prop_impl_unit_size                   0
% 1.58/1.00  --prop_impl_unit                        []
% 1.58/1.00  --share_sel_clauses                     true
% 1.58/1.00  --reset_solvers                         false
% 1.58/1.00  --bc_imp_inh                            [conj_cone]
% 1.58/1.00  --conj_cone_tolerance                   3.
% 1.58/1.00  --extra_neg_conj                        none
% 1.58/1.00  --large_theory_mode                     true
% 1.58/1.00  --prolific_symb_bound                   200
% 1.58/1.00  --lt_threshold                          2000
% 1.58/1.00  --clause_weak_htbl                      true
% 1.58/1.00  --gc_record_bc_elim                     false
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing Options
% 1.58/1.00  
% 1.58/1.00  --preprocessing_flag                    true
% 1.58/1.00  --time_out_prep_mult                    0.1
% 1.58/1.00  --splitting_mode                        input
% 1.58/1.00  --splitting_grd                         true
% 1.58/1.00  --splitting_cvd                         false
% 1.58/1.00  --splitting_cvd_svl                     false
% 1.58/1.00  --splitting_nvd                         32
% 1.58/1.00  --sub_typing                            true
% 1.58/1.00  --prep_gs_sim                           true
% 1.58/1.00  --prep_unflatten                        true
% 1.58/1.00  --prep_res_sim                          true
% 1.58/1.00  --prep_upred                            true
% 1.58/1.00  --prep_sem_filter                       exhaustive
% 1.58/1.00  --prep_sem_filter_out                   false
% 1.58/1.00  --pred_elim                             true
% 1.58/1.00  --res_sim_input                         true
% 1.58/1.00  --eq_ax_congr_red                       true
% 1.58/1.00  --pure_diseq_elim                       true
% 1.58/1.00  --brand_transform                       false
% 1.58/1.00  --non_eq_to_eq                          false
% 1.58/1.00  --prep_def_merge                        true
% 1.58/1.00  --prep_def_merge_prop_impl              false
% 1.58/1.00  --prep_def_merge_mbd                    true
% 1.58/1.00  --prep_def_merge_tr_red                 false
% 1.58/1.00  --prep_def_merge_tr_cl                  false
% 1.58/1.00  --smt_preprocessing                     true
% 1.58/1.00  --smt_ac_axioms                         fast
% 1.58/1.00  --preprocessed_out                      false
% 1.58/1.00  --preprocessed_stats                    false
% 1.58/1.00  
% 1.58/1.00  ------ Abstraction refinement Options
% 1.58/1.00  
% 1.58/1.00  --abstr_ref                             []
% 1.58/1.00  --abstr_ref_prep                        false
% 1.58/1.00  --abstr_ref_until_sat                   false
% 1.58/1.00  --abstr_ref_sig_restrict                funpre
% 1.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.00  --abstr_ref_under                       []
% 1.58/1.00  
% 1.58/1.00  ------ SAT Options
% 1.58/1.00  
% 1.58/1.00  --sat_mode                              false
% 1.58/1.00  --sat_fm_restart_options                ""
% 1.58/1.00  --sat_gr_def                            false
% 1.58/1.00  --sat_epr_types                         true
% 1.58/1.00  --sat_non_cyclic_types                  false
% 1.58/1.00  --sat_finite_models                     false
% 1.58/1.00  --sat_fm_lemmas                         false
% 1.58/1.00  --sat_fm_prep                           false
% 1.58/1.00  --sat_fm_uc_incr                        true
% 1.58/1.00  --sat_out_model                         small
% 1.58/1.00  --sat_out_clauses                       false
% 1.58/1.00  
% 1.58/1.00  ------ QBF Options
% 1.58/1.00  
% 1.58/1.00  --qbf_mode                              false
% 1.58/1.00  --qbf_elim_univ                         false
% 1.58/1.00  --qbf_dom_inst                          none
% 1.58/1.00  --qbf_dom_pre_inst                      false
% 1.58/1.00  --qbf_sk_in                             false
% 1.58/1.00  --qbf_pred_elim                         true
% 1.58/1.00  --qbf_split                             512
% 1.58/1.00  
% 1.58/1.00  ------ BMC1 Options
% 1.58/1.00  
% 1.58/1.00  --bmc1_incremental                      false
% 1.58/1.00  --bmc1_axioms                           reachable_all
% 1.58/1.00  --bmc1_min_bound                        0
% 1.58/1.00  --bmc1_max_bound                        -1
% 1.58/1.00  --bmc1_max_bound_default                -1
% 1.58/1.00  --bmc1_symbol_reachability              true
% 1.58/1.00  --bmc1_property_lemmas                  false
% 1.58/1.00  --bmc1_k_induction                      false
% 1.58/1.00  --bmc1_non_equiv_states                 false
% 1.58/1.00  --bmc1_deadlock                         false
% 1.58/1.00  --bmc1_ucm                              false
% 1.58/1.00  --bmc1_add_unsat_core                   none
% 1.58/1.00  --bmc1_unsat_core_children              false
% 1.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.00  --bmc1_out_stat                         full
% 1.58/1.00  --bmc1_ground_init                      false
% 1.58/1.00  --bmc1_pre_inst_next_state              false
% 1.58/1.00  --bmc1_pre_inst_state                   false
% 1.58/1.00  --bmc1_pre_inst_reach_state             false
% 1.58/1.00  --bmc1_out_unsat_core                   false
% 1.58/1.00  --bmc1_aig_witness_out                  false
% 1.58/1.00  --bmc1_verbose                          false
% 1.58/1.00  --bmc1_dump_clauses_tptp                false
% 1.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.00  --bmc1_dump_file                        -
% 1.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.00  --bmc1_ucm_extend_mode                  1
% 1.58/1.00  --bmc1_ucm_init_mode                    2
% 1.58/1.00  --bmc1_ucm_cone_mode                    none
% 1.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.00  --bmc1_ucm_relax_model                  4
% 1.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.00  --bmc1_ucm_layered_model                none
% 1.58/1.00  --bmc1_ucm_max_lemma_size               10
% 1.58/1.00  
% 1.58/1.00  ------ AIG Options
% 1.58/1.00  
% 1.58/1.00  --aig_mode                              false
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation Options
% 1.58/1.00  
% 1.58/1.00  --instantiation_flag                    true
% 1.58/1.00  --inst_sos_flag                         false
% 1.58/1.00  --inst_sos_phase                        true
% 1.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel_side                     none
% 1.58/1.00  --inst_solver_per_active                1400
% 1.58/1.00  --inst_solver_calls_frac                1.
% 1.58/1.00  --inst_passive_queue_type               priority_queues
% 1.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.00  --inst_passive_queues_freq              [25;2]
% 1.58/1.00  --inst_dismatching                      true
% 1.58/1.00  --inst_eager_unprocessed_to_passive     true
% 1.58/1.00  --inst_prop_sim_given                   true
% 1.58/1.00  --inst_prop_sim_new                     false
% 1.58/1.00  --inst_subs_new                         false
% 1.58/1.00  --inst_eq_res_simp                      false
% 1.58/1.00  --inst_subs_given                       false
% 1.58/1.00  --inst_orphan_elimination               true
% 1.58/1.00  --inst_learning_loop_flag               true
% 1.58/1.00  --inst_learning_start                   3000
% 1.58/1.00  --inst_learning_factor                  2
% 1.58/1.00  --inst_start_prop_sim_after_learn       3
% 1.58/1.00  --inst_sel_renew                        solver
% 1.58/1.00  --inst_lit_activity_flag                true
% 1.58/1.00  --inst_restr_to_given                   false
% 1.58/1.00  --inst_activity_threshold               500
% 1.58/1.00  --inst_out_proof                        true
% 1.58/1.00  
% 1.58/1.00  ------ Resolution Options
% 1.58/1.00  
% 1.58/1.00  --resolution_flag                       false
% 1.58/1.00  --res_lit_sel                           adaptive
% 1.58/1.00  --res_lit_sel_side                      none
% 1.58/1.00  --res_ordering                          kbo
% 1.58/1.00  --res_to_prop_solver                    active
% 1.58/1.00  --res_prop_simpl_new                    false
% 1.58/1.00  --res_prop_simpl_given                  true
% 1.58/1.00  --res_passive_queue_type                priority_queues
% 1.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.00  --res_passive_queues_freq               [15;5]
% 1.58/1.00  --res_forward_subs                      full
% 1.58/1.00  --res_backward_subs                     full
% 1.58/1.00  --res_forward_subs_resolution           true
% 1.58/1.00  --res_backward_subs_resolution          true
% 1.58/1.00  --res_orphan_elimination                true
% 1.58/1.00  --res_time_limit                        2.
% 1.58/1.00  --res_out_proof                         true
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Options
% 1.58/1.00  
% 1.58/1.00  --superposition_flag                    true
% 1.58/1.00  --sup_passive_queue_type                priority_queues
% 1.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.00  --demod_completeness_check              fast
% 1.58/1.00  --demod_use_ground                      true
% 1.58/1.00  --sup_to_prop_solver                    passive
% 1.58/1.00  --sup_prop_simpl_new                    true
% 1.58/1.00  --sup_prop_simpl_given                  true
% 1.58/1.00  --sup_fun_splitting                     false
% 1.58/1.00  --sup_smt_interval                      50000
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Simplification Setup
% 1.58/1.00  
% 1.58/1.00  --sup_indices_passive                   []
% 1.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_full_bw                           [BwDemod]
% 1.58/1.00  --sup_immed_triv                        [TrivRules]
% 1.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_immed_bw_main                     []
% 1.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  
% 1.58/1.00  ------ Combination Options
% 1.58/1.00  
% 1.58/1.00  --comb_res_mult                         3
% 1.58/1.00  --comb_sup_mult                         2
% 1.58/1.00  --comb_inst_mult                        10
% 1.58/1.00  
% 1.58/1.00  ------ Debug Options
% 1.58/1.00  
% 1.58/1.00  --dbg_backtrace                         false
% 1.58/1.00  --dbg_dump_prop_clauses                 false
% 1.58/1.00  --dbg_dump_prop_clauses_file            -
% 1.58/1.00  --dbg_out_stat                          false
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  ------ Proving...
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  % SZS status Theorem for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  fof(f1,axiom,(
% 1.58/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f25,plain,(
% 1.58/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.58/1.00    inference(nnf_transformation,[],[f1])).
% 1.58/1.00  
% 1.58/1.00  fof(f26,plain,(
% 1.58/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.58/1.00    inference(rectify,[],[f25])).
% 1.58/1.00  
% 1.58/1.00  fof(f27,plain,(
% 1.58/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f28,plain,(
% 1.58/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.58/1.00  
% 1.58/1.00  fof(f43,plain,(
% 1.58/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f28])).
% 1.58/1.00  
% 1.58/1.00  fof(f7,axiom,(
% 1.58/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f18,plain,(
% 1.58/1.00    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f7])).
% 1.58/1.00  
% 1.58/1.00  fof(f19,plain,(
% 1.58/1.00    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(flattening,[],[f18])).
% 1.58/1.00  
% 1.58/1.00  fof(f53,plain,(
% 1.58/1.00    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f19])).
% 1.58/1.00  
% 1.58/1.00  fof(f10,conjecture,(
% 1.58/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f11,negated_conjecture,(
% 1.58/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.58/1.00    inference(negated_conjecture,[],[f10])).
% 1.58/1.00  
% 1.58/1.00  fof(f23,plain,(
% 1.58/1.00    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f11])).
% 1.58/1.00  
% 1.58/1.00  fof(f24,plain,(
% 1.58/1.00    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.58/1.00    inference(flattening,[],[f23])).
% 1.58/1.00  
% 1.58/1.00  fof(f40,plain,(
% 1.58/1.00    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(X0))))) )),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f39,plain,(
% 1.58/1.00    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK5,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f41,plain,(
% 1.58/1.00    (k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) & m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f40,f39])).
% 1.58/1.00  
% 1.58/1.00  fof(f63,plain,(
% 1.58/1.00    m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5)))),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f62,plain,(
% 1.58/1.00    l1_orders_2(sK5)),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f58,plain,(
% 1.58/1.00    ~v2_struct_0(sK5)),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f59,plain,(
% 1.58/1.00    v3_orders_2(sK5)),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f60,plain,(
% 1.58/1.00    v4_orders_2(sK5)),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f61,plain,(
% 1.58/1.00    v5_orders_2(sK5)),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f64,plain,(
% 1.58/1.00    k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6))),
% 1.58/1.00    inference(cnf_transformation,[],[f41])).
% 1.58/1.00  
% 1.58/1.00  fof(f9,axiom,(
% 1.58/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f12,plain,(
% 1.58/1.00    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.58/1.00    inference(rectify,[],[f9])).
% 1.58/1.00  
% 1.58/1.00  fof(f22,plain,(
% 1.58/1.00    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.58/1.00    inference(ennf_transformation,[],[f12])).
% 1.58/1.00  
% 1.58/1.00  fof(f37,plain,(
% 1.58/1.00    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK4(X0),X0) & k1_xboole_0 != sK4(X0)))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f38,plain,(
% 1.58/1.00    ! [X0] : (((r2_hidden(sK4(X0),X0) & k1_xboole_0 != sK4(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f37])).
% 1.58/1.00  
% 1.58/1.00  fof(f55,plain,(
% 1.58/1.00    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.58/1.00    inference(cnf_transformation,[],[f38])).
% 1.58/1.00  
% 1.58/1.00  fof(f4,axiom,(
% 1.58/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f13,plain,(
% 1.58/1.00    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f4])).
% 1.58/1.00  
% 1.58/1.00  fof(f29,plain,(
% 1.58/1.00    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f30,plain,(
% 1.58/1.00    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f29])).
% 1.58/1.00  
% 1.58/1.00  fof(f46,plain,(
% 1.58/1.00    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f30])).
% 1.58/1.00  
% 1.58/1.00  fof(f42,plain,(
% 1.58/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f28])).
% 1.58/1.00  
% 1.58/1.00  fof(f2,axiom,(
% 1.58/1.00    v1_xboole_0(k1_xboole_0)),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f44,plain,(
% 1.58/1.00    v1_xboole_0(k1_xboole_0)),
% 1.58/1.00    inference(cnf_transformation,[],[f2])).
% 1.58/1.00  
% 1.58/1.00  fof(f3,axiom,(
% 1.58/1.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f45,plain,(
% 1.58/1.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.58/1.00    inference(cnf_transformation,[],[f3])).
% 1.58/1.00  
% 1.58/1.00  fof(f5,axiom,(
% 1.58/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f14,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f5])).
% 1.58/1.00  
% 1.58/1.00  fof(f15,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(flattening,[],[f14])).
% 1.58/1.00  
% 1.58/1.00  fof(f31,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(nnf_transformation,[],[f15])).
% 1.58/1.00  
% 1.58/1.00  fof(f32,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(rectify,[],[f31])).
% 1.58/1.00  
% 1.58/1.00  fof(f33,plain,(
% 1.58/1.00    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.58/1.00    introduced(choice_axiom,[])).
% 1.58/1.00  
% 1.58/1.00  fof(f34,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.58/1.00  
% 1.58/1.00  fof(f48,plain,(
% 1.58/1.00    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f34])).
% 1.58/1.00  
% 1.58/1.00  fof(f66,plain,(
% 1.58/1.00    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/1.00    inference(equality_resolution,[],[f48])).
% 1.58/1.00  
% 1.58/1.00  fof(f8,axiom,(
% 1.58/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.58/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.00  
% 1.58/1.00  fof(f20,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/1.00    inference(ennf_transformation,[],[f8])).
% 1.58/1.00  
% 1.58/1.00  fof(f21,plain,(
% 1.58/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.58/1.00    inference(flattening,[],[f20])).
% 1.58/1.00  
% 1.58/1.00  fof(f54,plain,(
% 1.58/1.00    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.58/1.00    inference(cnf_transformation,[],[f21])).
% 1.58/1.00  
% 1.58/1.00  cnf(c_0,plain,
% 1.58/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_11,plain,
% 1.58/1.00      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1)
% 1.58/1.00      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 1.58/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_17,negated_conjecture,
% 1.58/1.00      ( m1_orders_1(sK6,k1_orders_1(u1_struct_0(sK5))) ),
% 1.58/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_507,plain,
% 1.58/1.00      ( v2_struct_0(X0)
% 1.58/1.00      | ~ v3_orders_2(X0)
% 1.58/1.00      | ~ v4_orders_2(X0)
% 1.58/1.00      | ~ v5_orders_2(X0)
% 1.58/1.00      | ~ l1_orders_2(X0)
% 1.58/1.00      | ~ v1_xboole_0(k4_orders_2(X0,X1))
% 1.58/1.00      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK6 != X1 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_508,plain,
% 1.58/1.00      ( v2_struct_0(X0)
% 1.58/1.00      | ~ v3_orders_2(X0)
% 1.58/1.00      | ~ v4_orders_2(X0)
% 1.58/1.00      | ~ v5_orders_2(X0)
% 1.58/1.00      | ~ l1_orders_2(X0)
% 1.58/1.00      | ~ v1_xboole_0(k4_orders_2(X0,sK6))
% 1.58/1.00      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_507]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_18,negated_conjecture,
% 1.58/1.00      ( l1_orders_2(sK5) ),
% 1.58/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_685,plain,
% 1.58/1.00      ( v2_struct_0(X0)
% 1.58/1.00      | ~ v3_orders_2(X0)
% 1.58/1.00      | ~ v4_orders_2(X0)
% 1.58/1.00      | ~ v5_orders_2(X0)
% 1.58/1.00      | ~ v1_xboole_0(k4_orders_2(X0,sK6))
% 1.58/1.00      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK5 != X0 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_508,c_18]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_686,plain,
% 1.58/1.00      ( v2_struct_0(sK5)
% 1.58/1.00      | ~ v3_orders_2(sK5)
% 1.58/1.00      | ~ v4_orders_2(sK5)
% 1.58/1.00      | ~ v5_orders_2(sK5)
% 1.58/1.00      | ~ v1_xboole_0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_685]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_22,negated_conjecture,
% 1.58/1.00      ( ~ v2_struct_0(sK5) ),
% 1.58/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_21,negated_conjecture,
% 1.58/1.00      ( v3_orders_2(sK5) ),
% 1.58/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_20,negated_conjecture,
% 1.58/1.00      ( v4_orders_2(sK5) ),
% 1.58/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_19,negated_conjecture,
% 1.58/1.00      ( v5_orders_2(sK5) ),
% 1.58/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_688,plain,
% 1.58/1.00      ( ~ v1_xboole_0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_686,c_22,c_21,c_20,c_19]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_866,plain,
% 1.58/1.00      ( r2_hidden(sK0(X0),X0)
% 1.58/1.00      | k4_orders_2(sK5,sK6) != X0
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_688]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_867,plain,
% 1.58/1.00      ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_866]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1406,plain,
% 1.58/1.00      ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_16,negated_conjecture,
% 1.58/1.00      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK5,sK6)) ),
% 1.58/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_15,plain,
% 1.58/1.00      ( ~ r2_hidden(X0,X1)
% 1.58/1.00      | k3_tarski(X1) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = X0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1409,plain,
% 1.58/1.00      ( k3_tarski(X0) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = X1
% 1.58/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_2364,plain,
% 1.58/1.00      ( k1_xboole_0 = X0
% 1.58/1.00      | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
% 1.58/1.00      inference(superposition,[status(thm)],[c_16,c_1409]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_2438,plain,
% 1.58/1.00      ( sK0(k4_orders_2(sK5,sK6)) = k1_xboole_0 ),
% 1.58/1.00      inference(superposition,[status(thm)],[c_1406,c_2364]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_5,plain,
% 1.58/1.00      ( r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1411,plain,
% 1.58/1.00      ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
% 1.58/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1,plain,
% 1.58/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.58/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_2,plain,
% 1.58/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.58/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_873,plain,
% 1.58/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_874,plain,
% 1.58/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_873]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1407,plain,
% 1.58/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1909,plain,
% 1.58/1.00      ( r1_xboole_0(k3_tarski(k1_xboole_0),X0) = iProver_top ),
% 1.58/1.00      inference(superposition,[status(thm)],[c_1411,c_1407]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_3,plain,
% 1.58/1.00      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 1.58/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1917,plain,
% 1.58/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 1.58/1.00      inference(light_normalisation,[status(thm)],[c_1909,c_3]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1921,plain,
% 1.58/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1917]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1043,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1778,plain,
% 1.58/1.00      ( X0 != X1
% 1.58/1.00      | X0 = sK0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | sK0(k4_orders_2(sK5,sK6)) != X1 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1043]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1779,plain,
% 1.58/1.00      ( sK0(k4_orders_2(sK5,sK6)) != k1_xboole_0
% 1.58/1.00      | k1_xboole_0 = sK0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1778]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1042,plain,( X0 = X0 ),theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1637,plain,
% 1.58/1.00      ( k4_orders_2(sK5,sK6) = k4_orders_2(sK5,sK6) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1042]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1045,plain,
% 1.58/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.58/1.00      theory(equality) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1539,plain,
% 1.58/1.00      ( r2_hidden(X0,X1)
% 1.58/1.00      | ~ r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6))
% 1.58/1.00      | X1 != k4_orders_2(sK5,sK6)
% 1.58/1.00      | X0 != sK0(k4_orders_2(sK5,sK6)) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1045]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1636,plain,
% 1.58/1.00      ( r2_hidden(X0,k4_orders_2(sK5,sK6))
% 1.58/1.00      | ~ r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6))
% 1.58/1.00      | X0 != sK0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6) ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1539]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1638,plain,
% 1.58/1.00      ( X0 != sK0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6)
% 1.58/1.00      | r2_hidden(X0,k4_orders_2(sK5,sK6)) = iProver_top
% 1.58/1.00      | r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1640,plain,
% 1.58/1.00      ( k4_orders_2(sK5,sK6) != k4_orders_2(sK5,sK6)
% 1.58/1.00      | k1_xboole_0 != sK0(k4_orders_2(sK5,sK6))
% 1.58/1.00      | r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) != iProver_top
% 1.58/1.00      | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) = iProver_top ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_1061,plain,
% 1.58/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_1042]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_9,plain,
% 1.58/1.00      ( m2_orders_2(X0,X1,X2)
% 1.58/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1) ),
% 1.58/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_447,plain,
% 1.58/1.00      ( m2_orders_2(X0,X1,X2)
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK6 != X2 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_448,plain,
% 1.58/1.00      ( m2_orders_2(X0,X1,sK6)
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_447]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_782,plain,
% 1.58/1.00      ( m2_orders_2(X0,X1,sK6)
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(X1,sK6))
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK5 != X1 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_448,c_18]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_783,plain,
% 1.58/1.00      ( m2_orders_2(X0,sK5,sK6)
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
% 1.58/1.00      | v2_struct_0(sK5)
% 1.58/1.00      | ~ v3_orders_2(sK5)
% 1.58/1.00      | ~ v4_orders_2(sK5)
% 1.58/1.00      | ~ v5_orders_2(sK5)
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_782]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_787,plain,
% 1.58/1.00      ( m2_orders_2(X0,sK5,sK6)
% 1.58/1.00      | ~ r2_hidden(X0,k4_orders_2(sK5,sK6))
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_783,c_22,c_21,c_20,c_19]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_915,plain,
% 1.58/1.00      ( m2_orders_2(X0,sK5,sK6) | ~ r2_hidden(X0,k4_orders_2(sK5,sK6)) ),
% 1.58/1.00      inference(equality_resolution_simp,[status(thm)],[c_787]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_916,plain,
% 1.58/1.00      ( m2_orders_2(X0,sK5,sK6) = iProver_top
% 1.58/1.00      | r2_hidden(X0,k4_orders_2(sK5,sK6)) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_918,plain,
% 1.58/1.00      ( m2_orders_2(k1_xboole_0,sK5,sK6) = iProver_top
% 1.58/1.00      | r2_hidden(k1_xboole_0,k4_orders_2(sK5,sK6)) != iProver_top ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_916]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_12,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.58/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.58/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.58/1.00      | ~ r1_xboole_0(X3,X0)
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1) ),
% 1.58/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_414,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.58/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.58/1.00      | ~ r1_xboole_0(X3,X0)
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK6 != X2 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_415,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,X1,sK6)
% 1.58/1.00      | ~ m2_orders_2(X2,X1,sK6)
% 1.58/1.00      | ~ r1_xboole_0(X0,X2)
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | ~ l1_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_803,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,X1,sK6)
% 1.58/1.00      | ~ m2_orders_2(X2,X1,sK6)
% 1.58/1.00      | ~ r1_xboole_0(X0,X2)
% 1.58/1.00      | v2_struct_0(X1)
% 1.58/1.00      | ~ v3_orders_2(X1)
% 1.58/1.00      | ~ v4_orders_2(X1)
% 1.58/1.00      | ~ v5_orders_2(X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK5))
% 1.58/1.00      | sK5 != X1 ),
% 1.58/1.00      inference(resolution_lifted,[status(thm)],[c_415,c_18]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_804,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,sK5,sK6)
% 1.58/1.00      | ~ m2_orders_2(X1,sK5,sK6)
% 1.58/1.00      | ~ r1_xboole_0(X0,X1)
% 1.58/1.00      | v2_struct_0(sK5)
% 1.58/1.00      | ~ v3_orders_2(sK5)
% 1.58/1.00      | ~ v4_orders_2(sK5)
% 1.58/1.00      | ~ v5_orders_2(sK5)
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(unflattening,[status(thm)],[c_803]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_808,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,sK5,sK6)
% 1.58/1.00      | ~ m2_orders_2(X1,sK5,sK6)
% 1.58/1.00      | ~ r1_xboole_0(X0,X1)
% 1.58/1.00      | k1_orders_1(u1_struct_0(sK5)) != k1_orders_1(u1_struct_0(sK5)) ),
% 1.58/1.00      inference(global_propositional_subsumption,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_804,c_22,c_21,c_20,c_19]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_911,plain,
% 1.58/1.00      ( ~ m2_orders_2(X0,sK5,sK6)
% 1.58/1.00      | ~ m2_orders_2(X1,sK5,sK6)
% 1.58/1.00      | ~ r1_xboole_0(X0,X1) ),
% 1.58/1.00      inference(equality_resolution_simp,[status(thm)],[c_808]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_912,plain,
% 1.58/1.00      ( m2_orders_2(X0,sK5,sK6) != iProver_top
% 1.58/1.00      | m2_orders_2(X1,sK5,sK6) != iProver_top
% 1.58/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_914,plain,
% 1.58/1.00      ( m2_orders_2(k1_xboole_0,sK5,sK6) != iProver_top
% 1.58/1.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 1.58/1.00      inference(instantiation,[status(thm)],[c_912]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(c_868,plain,
% 1.58/1.00      ( r2_hidden(sK0(k4_orders_2(sK5,sK6)),k4_orders_2(sK5,sK6)) = iProver_top ),
% 1.58/1.00      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 1.58/1.00  
% 1.58/1.00  cnf(contradiction,plain,
% 1.58/1.00      ( $false ),
% 1.58/1.00      inference(minisat,
% 1.58/1.00                [status(thm)],
% 1.58/1.00                [c_2438,c_1921,c_1779,c_1637,c_1640,c_1061,c_918,c_914,
% 1.58/1.00                 c_868]) ).
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  ------                               Statistics
% 1.58/1.00  
% 1.58/1.00  ------ General
% 1.58/1.00  
% 1.58/1.00  abstr_ref_over_cycles:                  0
% 1.58/1.00  abstr_ref_under_cycles:                 0
% 1.58/1.00  gc_basic_clause_elim:                   0
% 1.58/1.00  forced_gc_time:                         0
% 1.58/1.00  parsing_time:                           0.009
% 1.58/1.00  unif_index_cands_time:                  0.
% 1.58/1.00  unif_index_add_time:                    0.
% 1.58/1.00  orderings_time:                         0.
% 1.58/1.00  out_proof_time:                         0.02
% 1.58/1.00  total_time:                             0.11
% 1.58/1.00  num_of_symbols:                         53
% 1.58/1.00  num_of_terms:                           1447
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing
% 1.58/1.00  
% 1.58/1.00  num_of_splits:                          0
% 1.58/1.00  num_of_split_atoms:                     0
% 1.58/1.00  num_of_reused_defs:                     0
% 1.58/1.00  num_eq_ax_congr_red:                    22
% 1.58/1.00  num_of_sem_filtered_clauses:            1
% 1.58/1.00  num_of_subtypes:                        0
% 1.58/1.00  monotx_restored_types:                  0
% 1.58/1.00  sat_num_of_epr_types:                   0
% 1.58/1.00  sat_num_of_non_cyclic_types:            0
% 1.58/1.00  sat_guarded_non_collapsed_types:        0
% 1.58/1.00  num_pure_diseq_elim:                    0
% 1.58/1.00  simp_replaced_by:                       0
% 1.58/1.00  res_preprocessed:                       95
% 1.58/1.00  prep_upred:                             0
% 1.58/1.00  prep_unflattend:                        23
% 1.58/1.00  smt_new_axioms:                         0
% 1.58/1.00  pred_elim_cands:                        3
% 1.58/1.00  pred_elim:                              7
% 1.58/1.00  pred_elim_cl:                           6
% 1.58/1.00  pred_elim_cycles:                       11
% 1.58/1.00  merged_defs:                            6
% 1.58/1.00  merged_defs_ncl:                        0
% 1.58/1.00  bin_hyper_res:                          6
% 1.58/1.00  prep_cycles:                            4
% 1.58/1.00  pred_elim_time:                         0.014
% 1.58/1.00  splitting_time:                         0.
% 1.58/1.00  sem_filter_time:                        0.
% 1.58/1.00  monotx_time:                            0.001
% 1.58/1.00  subtype_inf_time:                       0.
% 1.58/1.00  
% 1.58/1.00  ------ Problem properties
% 1.58/1.00  
% 1.58/1.00  clauses:                                17
% 1.58/1.00  conjectures:                            1
% 1.58/1.00  epr:                                    2
% 1.58/1.00  horn:                                   14
% 1.58/1.00  ground:                                 5
% 1.58/1.00  unary:                                  6
% 1.58/1.00  binary:                                 7
% 1.58/1.00  lits:                                   32
% 1.58/1.00  lits_eq:                                10
% 1.58/1.00  fd_pure:                                0
% 1.58/1.00  fd_pseudo:                              0
% 1.58/1.00  fd_cond:                                3
% 1.58/1.00  fd_pseudo_cond:                         0
% 1.58/1.00  ac_symbols:                             0
% 1.58/1.00  
% 1.58/1.00  ------ Propositional Solver
% 1.58/1.00  
% 1.58/1.00  prop_solver_calls:                      26
% 1.58/1.00  prop_fast_solver_calls:                 694
% 1.58/1.00  smt_solver_calls:                       0
% 1.58/1.00  smt_fast_solver_calls:                  0
% 1.58/1.00  prop_num_of_clauses:                    641
% 1.58/1.00  prop_preprocess_simplified:             3053
% 1.58/1.00  prop_fo_subsumed:                       29
% 1.58/1.00  prop_solver_time:                       0.
% 1.58/1.00  smt_solver_time:                        0.
% 1.58/1.00  smt_fast_solver_time:                   0.
% 1.58/1.00  prop_fast_solver_time:                  0.
% 1.58/1.00  prop_unsat_core_time:                   0.
% 1.58/1.00  
% 1.58/1.00  ------ QBF
% 1.58/1.00  
% 1.58/1.00  qbf_q_res:                              0
% 1.58/1.00  qbf_num_tautologies:                    0
% 1.58/1.00  qbf_prep_cycles:                        0
% 1.58/1.00  
% 1.58/1.00  ------ BMC1
% 1.58/1.00  
% 1.58/1.00  bmc1_current_bound:                     -1
% 1.58/1.00  bmc1_last_solved_bound:                 -1
% 1.58/1.00  bmc1_unsat_core_size:                   -1
% 1.58/1.00  bmc1_unsat_core_parents_size:           -1
% 1.58/1.00  bmc1_merge_next_fun:                    0
% 1.58/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation
% 1.58/1.00  
% 1.58/1.00  inst_num_of_clauses:                    166
% 1.58/1.00  inst_num_in_passive:                    2
% 1.58/1.00  inst_num_in_active:                     114
% 1.58/1.00  inst_num_in_unprocessed:                50
% 1.58/1.00  inst_num_of_loops:                      130
% 1.58/1.00  inst_num_of_learning_restarts:          0
% 1.58/1.00  inst_num_moves_active_passive:          14
% 1.58/1.00  inst_lit_activity:                      0
% 1.58/1.00  inst_lit_activity_moves:                0
% 1.58/1.00  inst_num_tautologies:                   0
% 1.58/1.00  inst_num_prop_implied:                  0
% 1.58/1.00  inst_num_existing_simplified:           0
% 1.58/1.00  inst_num_eq_res_simplified:             0
% 1.58/1.00  inst_num_child_elim:                    0
% 1.58/1.00  inst_num_of_dismatching_blockings:      17
% 1.58/1.00  inst_num_of_non_proper_insts:           140
% 1.58/1.00  inst_num_of_duplicates:                 0
% 1.58/1.00  inst_inst_num_from_inst_to_res:         0
% 1.58/1.00  inst_dismatching_checking_time:         0.
% 1.58/1.00  
% 1.58/1.00  ------ Resolution
% 1.58/1.00  
% 1.58/1.00  res_num_of_clauses:                     0
% 1.58/1.00  res_num_in_passive:                     0
% 1.58/1.00  res_num_in_active:                      0
% 1.58/1.00  res_num_of_loops:                       99
% 1.58/1.00  res_forward_subset_subsumed:            24
% 1.58/1.00  res_backward_subset_subsumed:           0
% 1.58/1.00  res_forward_subsumed:                   0
% 1.58/1.00  res_backward_subsumed:                  0
% 1.58/1.00  res_forward_subsumption_resolution:     0
% 1.58/1.00  res_backward_subsumption_resolution:    0
% 1.58/1.00  res_clause_to_clause_subsumption:       51
% 1.58/1.00  res_orphan_elimination:                 0
% 1.58/1.00  res_tautology_del:                      30
% 1.58/1.00  res_num_eq_res_simplified:              7
% 1.58/1.00  res_num_sel_changes:                    0
% 1.58/1.00  res_moves_from_active_to_pass:          0
% 1.58/1.00  
% 1.58/1.00  ------ Superposition
% 1.58/1.00  
% 1.58/1.00  sup_time_total:                         0.
% 1.58/1.00  sup_time_generating:                    0.
% 1.58/1.00  sup_time_sim_full:                      0.
% 1.58/1.00  sup_time_sim_immed:                     0.
% 1.58/1.00  
% 1.58/1.00  sup_num_of_clauses:                     30
% 1.58/1.00  sup_num_in_active:                      25
% 1.58/1.00  sup_num_in_passive:                     5
% 1.58/1.00  sup_num_of_loops:                       24
% 1.58/1.00  sup_fw_superposition:                   23
% 1.58/1.00  sup_bw_superposition:                   8
% 1.58/1.00  sup_immediate_simplified:               9
% 1.58/1.00  sup_given_eliminated:                   0
% 1.58/1.00  comparisons_done:                       0
% 1.58/1.00  comparisons_avoided:                    0
% 1.58/1.00  
% 1.58/1.00  ------ Simplifications
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  sim_fw_subset_subsumed:                 2
% 1.58/1.00  sim_bw_subset_subsumed:                 0
% 1.58/1.00  sim_fw_subsumed:                        4
% 1.58/1.00  sim_bw_subsumed:                        0
% 1.58/1.00  sim_fw_subsumption_res:                 0
% 1.58/1.00  sim_bw_subsumption_res:                 0
% 1.58/1.00  sim_tautology_del:                      2
% 1.58/1.00  sim_eq_tautology_del:                   6
% 1.58/1.00  sim_eq_res_simp:                        0
% 1.58/1.00  sim_fw_demodulated:                     2
% 1.58/1.00  sim_bw_demodulated:                     0
% 1.58/1.00  sim_light_normalised:                   3
% 1.58/1.00  sim_joinable_taut:                      0
% 1.58/1.00  sim_joinable_simp:                      0
% 1.58/1.00  sim_ac_normalised:                      0
% 1.58/1.00  sim_smt_subsumption:                    0
% 1.58/1.00  
%------------------------------------------------------------------------------
