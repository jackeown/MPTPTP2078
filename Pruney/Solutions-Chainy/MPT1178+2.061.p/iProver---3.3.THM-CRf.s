%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:09 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 552 expanded)
%              Number of clauses        :   76 ( 136 expanded)
%              Number of leaves         :   15 ( 155 expanded)
%              Depth                    :   20
%              Number of atoms          :  613 (3398 expanded)
%              Number of equality atoms :  165 ( 618 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_orders_2(X0,X1) = X2
      | m2_orders_2(sK1(X0,X1,X2),X0,X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4))
        & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3))) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))
    & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f32,f31])).

fof(f54,plain,(
    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f55,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f29])).

fof(f46,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_orders_2(X0,X1) = X2
      | ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_273,plain,
    ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_274,plain,
    ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_546,plain,
    ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_17])).

cnf(c_547,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_551,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_21,c_20,c_19,c_18])).

cnf(c_1136,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_551])).

cnf(c_1957,plain,
    ( k4_orders_2(sK3,sK4) = X0
    | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_8,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_399,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_400,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_570,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_400,c_17])).

cnf(c_571,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_21,c_20,c_19,c_18])).

cnf(c_1134,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_575])).

cnf(c_1167,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(prop_impl,[status(thm)],[c_1134])).

cnf(c_1958,plain,
    ( m2_orders_2(X0,sK3,sK4) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1962,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2573,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1962])).

cnf(c_2659,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_2573])).

cnf(c_2681,plain,
    ( sK1(sK3,sK4,X0) = k1_xboole_0
    | k4_orders_2(sK3,sK4) = X0
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_2659])).

cnf(c_2693,plain,
    ( sK1(sK3,sK4,k1_xboole_0) = k1_xboole_0
    | k4_orders_2(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2681])).

cnf(c_1658,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2071,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK1(sK3,sK4,X3),sK3,sK4)
    | X0 != sK1(sK3,sK4,X3)
    | X2 != sK4
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_2410,plain,
    ( m2_orders_2(X0,sK3,X1)
    | ~ m2_orders_2(sK1(sK3,sK4,X2),sK3,sK4)
    | X0 != sK1(sK3,sK4,X2)
    | X1 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_2589,plain,
    ( m2_orders_2(X0,sK3,sK4)
    | ~ m2_orders_2(sK1(sK3,sK4,X1),sK3,sK4)
    | X0 != sK1(sK3,sK4,X1)
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_2591,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
    | m2_orders_2(k1_xboole_0,sK3,sK4)
    | sK4 != sK4
    | sK3 != sK3
    | k1_xboole_0 != sK1(sK3,sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_1653,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2411,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_2192,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_1654,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2123,plain,
    ( X0 != X1
    | X0 = sK1(sK3,sK4,X2)
    | sK1(sK3,sK4,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_2124,plain,
    ( sK1(sK3,sK4,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = sK1(sK3,sK4,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_1670,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_239,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k4_orders_2(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_429,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_16])).

cnf(c_430,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_511,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_17])).

cnf(c_512,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( k4_orders_2(sK3,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_21,c_20,c_19,c_18])).

cnf(c_1142,plain,
    ( k4_orders_2(sK3,sK4) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_514])).

cnf(c_6,plain,
    ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_306,plain,
    ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_307,plain,
    ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_522,plain,
    ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_307,c_17])).

cnf(c_523,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_21,c_20,c_19,c_18])).

cnf(c_1138,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_527])).

cnf(c_1139,plain,
    ( k4_orders_2(sK3,sK4) = X0
    | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) != iProver_top
    | r2_hidden(sK1(sK3,sK4,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_1141,plain,
    ( k4_orders_2(sK3,sK4) = k1_xboole_0
    | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_339,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_340,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_612,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_340,c_17])).

cnf(c_613,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_21,c_20,c_19,c_18])).

cnf(c_1013,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | k1_funct_1(sK4,u1_struct_0(sK3)) != X1
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_617])).

cnf(c_1014,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_991,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | sK1(sK3,sK4,X0) != X1
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_551])).

cnf(c_992,plain,
    ( m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
    | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_993,plain,
    ( k4_orders_2(sK3,sK4) = k1_xboole_0
    | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2693,c_2591,c_2411,c_2192,c_2124,c_1670,c_1142,c_1141,c_1014,c_993,c_992])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.25/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.25/0.99  
% 1.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.25/0.99  
% 1.25/0.99  ------  iProver source info
% 1.25/0.99  
% 1.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.25/0.99  git: non_committed_changes: false
% 1.25/0.99  git: last_make_outside_of_git: false
% 1.25/0.99  
% 1.25/0.99  ------ 
% 1.25/0.99  
% 1.25/0.99  ------ Input Options
% 1.25/0.99  
% 1.25/0.99  --out_options                           all
% 1.25/0.99  --tptp_safe_out                         true
% 1.25/0.99  --problem_path                          ""
% 1.25/0.99  --include_path                          ""
% 1.25/0.99  --clausifier                            res/vclausify_rel
% 1.25/0.99  --clausifier_options                    --mode clausify
% 1.25/0.99  --stdin                                 false
% 1.25/0.99  --stats_out                             all
% 1.25/0.99  
% 1.25/0.99  ------ General Options
% 1.25/0.99  
% 1.25/0.99  --fof                                   false
% 1.25/0.99  --time_out_real                         305.
% 1.25/0.99  --time_out_virtual                      -1.
% 1.25/0.99  --symbol_type_check                     false
% 1.25/0.99  --clausify_out                          false
% 1.25/0.99  --sig_cnt_out                           false
% 1.25/0.99  --trig_cnt_out                          false
% 1.25/0.99  --trig_cnt_out_tolerance                1.
% 1.25/0.99  --trig_cnt_out_sk_spl                   false
% 1.25/0.99  --abstr_cl_out                          false
% 1.25/0.99  
% 1.25/0.99  ------ Global Options
% 1.25/0.99  
% 1.25/0.99  --schedule                              default
% 1.25/0.99  --add_important_lit                     false
% 1.25/0.99  --prop_solver_per_cl                    1000
% 1.25/0.99  --min_unsat_core                        false
% 1.25/0.99  --soft_assumptions                      false
% 1.25/0.99  --soft_lemma_size                       3
% 1.25/0.99  --prop_impl_unit_size                   0
% 1.25/0.99  --prop_impl_unit                        []
% 1.25/0.99  --share_sel_clauses                     true
% 1.25/0.99  --reset_solvers                         false
% 1.25/0.99  --bc_imp_inh                            [conj_cone]
% 1.25/0.99  --conj_cone_tolerance                   3.
% 1.25/0.99  --extra_neg_conj                        none
% 1.25/0.99  --large_theory_mode                     true
% 1.25/0.99  --prolific_symb_bound                   200
% 1.25/0.99  --lt_threshold                          2000
% 1.25/0.99  --clause_weak_htbl                      true
% 1.25/0.99  --gc_record_bc_elim                     false
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing Options
% 1.25/0.99  
% 1.25/0.99  --preprocessing_flag                    true
% 1.25/0.99  --time_out_prep_mult                    0.1
% 1.25/0.99  --splitting_mode                        input
% 1.25/0.99  --splitting_grd                         true
% 1.25/0.99  --splitting_cvd                         false
% 1.25/0.99  --splitting_cvd_svl                     false
% 1.25/0.99  --splitting_nvd                         32
% 1.25/0.99  --sub_typing                            true
% 1.25/0.99  --prep_gs_sim                           true
% 1.25/0.99  --prep_unflatten                        true
% 1.25/0.99  --prep_res_sim                          true
% 1.25/0.99  --prep_upred                            true
% 1.25/0.99  --prep_sem_filter                       exhaustive
% 1.25/0.99  --prep_sem_filter_out                   false
% 1.25/0.99  --pred_elim                             true
% 1.25/0.99  --res_sim_input                         true
% 1.25/0.99  --eq_ax_congr_red                       true
% 1.25/0.99  --pure_diseq_elim                       true
% 1.25/0.99  --brand_transform                       false
% 1.25/0.99  --non_eq_to_eq                          false
% 1.25/0.99  --prep_def_merge                        true
% 1.25/0.99  --prep_def_merge_prop_impl              false
% 1.25/0.99  --prep_def_merge_mbd                    true
% 1.25/0.99  --prep_def_merge_tr_red                 false
% 1.25/0.99  --prep_def_merge_tr_cl                  false
% 1.25/0.99  --smt_preprocessing                     true
% 1.25/0.99  --smt_ac_axioms                         fast
% 1.25/0.99  --preprocessed_out                      false
% 1.25/0.99  --preprocessed_stats                    false
% 1.25/0.99  
% 1.25/0.99  ------ Abstraction refinement Options
% 1.25/0.99  
% 1.25/0.99  --abstr_ref                             []
% 1.25/0.99  --abstr_ref_prep                        false
% 1.25/0.99  --abstr_ref_until_sat                   false
% 1.25/0.99  --abstr_ref_sig_restrict                funpre
% 1.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.25/0.99  --abstr_ref_under                       []
% 1.25/0.99  
% 1.25/0.99  ------ SAT Options
% 1.25/0.99  
% 1.25/0.99  --sat_mode                              false
% 1.25/0.99  --sat_fm_restart_options                ""
% 1.25/0.99  --sat_gr_def                            false
% 1.25/0.99  --sat_epr_types                         true
% 1.25/0.99  --sat_non_cyclic_types                  false
% 1.25/0.99  --sat_finite_models                     false
% 1.25/0.99  --sat_fm_lemmas                         false
% 1.25/0.99  --sat_fm_prep                           false
% 1.25/0.99  --sat_fm_uc_incr                        true
% 1.25/0.99  --sat_out_model                         small
% 1.25/0.99  --sat_out_clauses                       false
% 1.25/0.99  
% 1.25/0.99  ------ QBF Options
% 1.25/0.99  
% 1.25/0.99  --qbf_mode                              false
% 1.25/0.99  --qbf_elim_univ                         false
% 1.25/0.99  --qbf_dom_inst                          none
% 1.25/0.99  --qbf_dom_pre_inst                      false
% 1.25/0.99  --qbf_sk_in                             false
% 1.25/0.99  --qbf_pred_elim                         true
% 1.25/0.99  --qbf_split                             512
% 1.25/0.99  
% 1.25/0.99  ------ BMC1 Options
% 1.25/0.99  
% 1.25/0.99  --bmc1_incremental                      false
% 1.25/0.99  --bmc1_axioms                           reachable_all
% 1.25/0.99  --bmc1_min_bound                        0
% 1.25/0.99  --bmc1_max_bound                        -1
% 1.25/0.99  --bmc1_max_bound_default                -1
% 1.25/0.99  --bmc1_symbol_reachability              true
% 1.25/0.99  --bmc1_property_lemmas                  false
% 1.25/0.99  --bmc1_k_induction                      false
% 1.25/0.99  --bmc1_non_equiv_states                 false
% 1.25/0.99  --bmc1_deadlock                         false
% 1.25/0.99  --bmc1_ucm                              false
% 1.25/0.99  --bmc1_add_unsat_core                   none
% 1.25/0.99  --bmc1_unsat_core_children              false
% 1.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.25/0.99  --bmc1_out_stat                         full
% 1.25/0.99  --bmc1_ground_init                      false
% 1.25/0.99  --bmc1_pre_inst_next_state              false
% 1.25/0.99  --bmc1_pre_inst_state                   false
% 1.25/0.99  --bmc1_pre_inst_reach_state             false
% 1.25/0.99  --bmc1_out_unsat_core                   false
% 1.25/0.99  --bmc1_aig_witness_out                  false
% 1.25/0.99  --bmc1_verbose                          false
% 1.25/0.99  --bmc1_dump_clauses_tptp                false
% 1.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.25/0.99  --bmc1_dump_file                        -
% 1.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.25/0.99  --bmc1_ucm_extend_mode                  1
% 1.25/0.99  --bmc1_ucm_init_mode                    2
% 1.25/0.99  --bmc1_ucm_cone_mode                    none
% 1.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.25/0.99  --bmc1_ucm_relax_model                  4
% 1.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.25/0.99  --bmc1_ucm_layered_model                none
% 1.25/0.99  --bmc1_ucm_max_lemma_size               10
% 1.25/0.99  
% 1.25/0.99  ------ AIG Options
% 1.25/0.99  
% 1.25/0.99  --aig_mode                              false
% 1.25/0.99  
% 1.25/0.99  ------ Instantiation Options
% 1.25/0.99  
% 1.25/0.99  --instantiation_flag                    true
% 1.25/0.99  --inst_sos_flag                         false
% 1.25/0.99  --inst_sos_phase                        true
% 1.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.25/0.99  --inst_lit_sel_side                     num_symb
% 1.25/0.99  --inst_solver_per_active                1400
% 1.25/0.99  --inst_solver_calls_frac                1.
% 1.25/0.99  --inst_passive_queue_type               priority_queues
% 1.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.25/0.99  --inst_passive_queues_freq              [25;2]
% 1.25/0.99  --inst_dismatching                      true
% 1.25/0.99  --inst_eager_unprocessed_to_passive     true
% 1.25/0.99  --inst_prop_sim_given                   true
% 1.25/0.99  --inst_prop_sim_new                     false
% 1.25/0.99  --inst_subs_new                         false
% 1.25/0.99  --inst_eq_res_simp                      false
% 1.25/0.99  --inst_subs_given                       false
% 1.25/0.99  --inst_orphan_elimination               true
% 1.25/0.99  --inst_learning_loop_flag               true
% 1.25/0.99  --inst_learning_start                   3000
% 1.25/0.99  --inst_learning_factor                  2
% 1.25/0.99  --inst_start_prop_sim_after_learn       3
% 1.25/0.99  --inst_sel_renew                        solver
% 1.25/0.99  --inst_lit_activity_flag                true
% 1.25/0.99  --inst_restr_to_given                   false
% 1.25/0.99  --inst_activity_threshold               500
% 1.25/0.99  --inst_out_proof                        true
% 1.25/0.99  
% 1.25/0.99  ------ Resolution Options
% 1.25/0.99  
% 1.25/0.99  --resolution_flag                       true
% 1.25/0.99  --res_lit_sel                           adaptive
% 1.25/0.99  --res_lit_sel_side                      none
% 1.25/0.99  --res_ordering                          kbo
% 1.25/0.99  --res_to_prop_solver                    active
% 1.25/0.99  --res_prop_simpl_new                    false
% 1.25/0.99  --res_prop_simpl_given                  true
% 1.25/0.99  --res_passive_queue_type                priority_queues
% 1.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.25/0.99  --res_passive_queues_freq               [15;5]
% 1.25/0.99  --res_forward_subs                      full
% 1.25/0.99  --res_backward_subs                     full
% 1.25/0.99  --res_forward_subs_resolution           true
% 1.25/0.99  --res_backward_subs_resolution          true
% 1.25/0.99  --res_orphan_elimination                true
% 1.25/0.99  --res_time_limit                        2.
% 1.25/0.99  --res_out_proof                         true
% 1.25/0.99  
% 1.25/0.99  ------ Superposition Options
% 1.25/0.99  
% 1.25/0.99  --superposition_flag                    true
% 1.25/0.99  --sup_passive_queue_type                priority_queues
% 1.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.25/0.99  --demod_completeness_check              fast
% 1.25/0.99  --demod_use_ground                      true
% 1.25/0.99  --sup_to_prop_solver                    passive
% 1.25/0.99  --sup_prop_simpl_new                    true
% 1.25/0.99  --sup_prop_simpl_given                  true
% 1.25/0.99  --sup_fun_splitting                     false
% 1.25/0.99  --sup_smt_interval                      50000
% 1.25/0.99  
% 1.25/0.99  ------ Superposition Simplification Setup
% 1.25/0.99  
% 1.25/0.99  --sup_indices_passive                   []
% 1.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_full_bw                           [BwDemod]
% 1.25/0.99  --sup_immed_triv                        [TrivRules]
% 1.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_immed_bw_main                     []
% 1.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/0.99  
% 1.25/0.99  ------ Combination Options
% 1.25/0.99  
% 1.25/0.99  --comb_res_mult                         3
% 1.25/0.99  --comb_sup_mult                         2
% 1.25/0.99  --comb_inst_mult                        10
% 1.25/0.99  
% 1.25/0.99  ------ Debug Options
% 1.25/0.99  
% 1.25/0.99  --dbg_backtrace                         false
% 1.25/0.99  --dbg_dump_prop_clauses                 false
% 1.25/0.99  --dbg_dump_prop_clauses_file            -
% 1.25/0.99  --dbg_out_stat                          false
% 1.25/0.99  ------ Parsing...
% 1.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.25/0.99  ------ Proving...
% 1.25/0.99  ------ Problem Properties 
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  clauses                                 14
% 1.25/0.99  conjectures                             1
% 1.25/0.99  EPR                                     1
% 1.25/0.99  Horn                                    11
% 1.25/0.99  unary                                   3
% 1.25/0.99  binary                                  6
% 1.25/0.99  lits                                    30
% 1.25/0.99  lits eq                                 14
% 1.25/0.99  fd_pure                                 0
% 1.25/0.99  fd_pseudo                               0
% 1.25/0.99  fd_cond                                 6
% 1.25/0.99  fd_pseudo_cond                          0
% 1.25/0.99  AC symbols                              0
% 1.25/0.99  
% 1.25/0.99  ------ Schedule dynamic 5 is on 
% 1.25/0.99  
% 1.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  ------ 
% 1.25/0.99  Current options:
% 1.25/0.99  ------ 
% 1.25/0.99  
% 1.25/0.99  ------ Input Options
% 1.25/0.99  
% 1.25/0.99  --out_options                           all
% 1.25/0.99  --tptp_safe_out                         true
% 1.25/0.99  --problem_path                          ""
% 1.25/0.99  --include_path                          ""
% 1.25/0.99  --clausifier                            res/vclausify_rel
% 1.25/0.99  --clausifier_options                    --mode clausify
% 1.25/0.99  --stdin                                 false
% 1.25/0.99  --stats_out                             all
% 1.25/0.99  
% 1.25/0.99  ------ General Options
% 1.25/0.99  
% 1.25/0.99  --fof                                   false
% 1.25/0.99  --time_out_real                         305.
% 1.25/0.99  --time_out_virtual                      -1.
% 1.25/0.99  --symbol_type_check                     false
% 1.25/0.99  --clausify_out                          false
% 1.25/0.99  --sig_cnt_out                           false
% 1.25/0.99  --trig_cnt_out                          false
% 1.25/0.99  --trig_cnt_out_tolerance                1.
% 1.25/0.99  --trig_cnt_out_sk_spl                   false
% 1.25/0.99  --abstr_cl_out                          false
% 1.25/0.99  
% 1.25/0.99  ------ Global Options
% 1.25/0.99  
% 1.25/0.99  --schedule                              default
% 1.25/0.99  --add_important_lit                     false
% 1.25/0.99  --prop_solver_per_cl                    1000
% 1.25/0.99  --min_unsat_core                        false
% 1.25/0.99  --soft_assumptions                      false
% 1.25/0.99  --soft_lemma_size                       3
% 1.25/0.99  --prop_impl_unit_size                   0
% 1.25/0.99  --prop_impl_unit                        []
% 1.25/0.99  --share_sel_clauses                     true
% 1.25/0.99  --reset_solvers                         false
% 1.25/0.99  --bc_imp_inh                            [conj_cone]
% 1.25/0.99  --conj_cone_tolerance                   3.
% 1.25/0.99  --extra_neg_conj                        none
% 1.25/0.99  --large_theory_mode                     true
% 1.25/0.99  --prolific_symb_bound                   200
% 1.25/0.99  --lt_threshold                          2000
% 1.25/0.99  --clause_weak_htbl                      true
% 1.25/0.99  --gc_record_bc_elim                     false
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing Options
% 1.25/0.99  
% 1.25/0.99  --preprocessing_flag                    true
% 1.25/0.99  --time_out_prep_mult                    0.1
% 1.25/0.99  --splitting_mode                        input
% 1.25/0.99  --splitting_grd                         true
% 1.25/0.99  --splitting_cvd                         false
% 1.25/0.99  --splitting_cvd_svl                     false
% 1.25/0.99  --splitting_nvd                         32
% 1.25/0.99  --sub_typing                            true
% 1.25/0.99  --prep_gs_sim                           true
% 1.25/0.99  --prep_unflatten                        true
% 1.25/0.99  --prep_res_sim                          true
% 1.25/0.99  --prep_upred                            true
% 1.25/0.99  --prep_sem_filter                       exhaustive
% 1.25/0.99  --prep_sem_filter_out                   false
% 1.25/0.99  --pred_elim                             true
% 1.25/0.99  --res_sim_input                         true
% 1.25/0.99  --eq_ax_congr_red                       true
% 1.25/0.99  --pure_diseq_elim                       true
% 1.25/0.99  --brand_transform                       false
% 1.25/0.99  --non_eq_to_eq                          false
% 1.25/0.99  --prep_def_merge                        true
% 1.25/0.99  --prep_def_merge_prop_impl              false
% 1.25/0.99  --prep_def_merge_mbd                    true
% 1.25/0.99  --prep_def_merge_tr_red                 false
% 1.25/0.99  --prep_def_merge_tr_cl                  false
% 1.25/0.99  --smt_preprocessing                     true
% 1.25/0.99  --smt_ac_axioms                         fast
% 1.25/0.99  --preprocessed_out                      false
% 1.25/0.99  --preprocessed_stats                    false
% 1.25/0.99  
% 1.25/0.99  ------ Abstraction refinement Options
% 1.25/0.99  
% 1.25/0.99  --abstr_ref                             []
% 1.25/0.99  --abstr_ref_prep                        false
% 1.25/0.99  --abstr_ref_until_sat                   false
% 1.25/0.99  --abstr_ref_sig_restrict                funpre
% 1.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.25/0.99  --abstr_ref_under                       []
% 1.25/0.99  
% 1.25/0.99  ------ SAT Options
% 1.25/0.99  
% 1.25/0.99  --sat_mode                              false
% 1.25/0.99  --sat_fm_restart_options                ""
% 1.25/0.99  --sat_gr_def                            false
% 1.25/0.99  --sat_epr_types                         true
% 1.25/0.99  --sat_non_cyclic_types                  false
% 1.25/0.99  --sat_finite_models                     false
% 1.25/0.99  --sat_fm_lemmas                         false
% 1.25/0.99  --sat_fm_prep                           false
% 1.25/0.99  --sat_fm_uc_incr                        true
% 1.25/0.99  --sat_out_model                         small
% 1.25/0.99  --sat_out_clauses                       false
% 1.25/0.99  
% 1.25/0.99  ------ QBF Options
% 1.25/0.99  
% 1.25/0.99  --qbf_mode                              false
% 1.25/0.99  --qbf_elim_univ                         false
% 1.25/0.99  --qbf_dom_inst                          none
% 1.25/0.99  --qbf_dom_pre_inst                      false
% 1.25/0.99  --qbf_sk_in                             false
% 1.25/0.99  --qbf_pred_elim                         true
% 1.25/0.99  --qbf_split                             512
% 1.25/0.99  
% 1.25/0.99  ------ BMC1 Options
% 1.25/0.99  
% 1.25/0.99  --bmc1_incremental                      false
% 1.25/0.99  --bmc1_axioms                           reachable_all
% 1.25/0.99  --bmc1_min_bound                        0
% 1.25/0.99  --bmc1_max_bound                        -1
% 1.25/0.99  --bmc1_max_bound_default                -1
% 1.25/0.99  --bmc1_symbol_reachability              true
% 1.25/0.99  --bmc1_property_lemmas                  false
% 1.25/0.99  --bmc1_k_induction                      false
% 1.25/0.99  --bmc1_non_equiv_states                 false
% 1.25/0.99  --bmc1_deadlock                         false
% 1.25/0.99  --bmc1_ucm                              false
% 1.25/0.99  --bmc1_add_unsat_core                   none
% 1.25/0.99  --bmc1_unsat_core_children              false
% 1.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.25/0.99  --bmc1_out_stat                         full
% 1.25/0.99  --bmc1_ground_init                      false
% 1.25/0.99  --bmc1_pre_inst_next_state              false
% 1.25/0.99  --bmc1_pre_inst_state                   false
% 1.25/0.99  --bmc1_pre_inst_reach_state             false
% 1.25/0.99  --bmc1_out_unsat_core                   false
% 1.25/0.99  --bmc1_aig_witness_out                  false
% 1.25/0.99  --bmc1_verbose                          false
% 1.25/0.99  --bmc1_dump_clauses_tptp                false
% 1.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.25/0.99  --bmc1_dump_file                        -
% 1.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.25/0.99  --bmc1_ucm_extend_mode                  1
% 1.25/0.99  --bmc1_ucm_init_mode                    2
% 1.25/0.99  --bmc1_ucm_cone_mode                    none
% 1.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.25/0.99  --bmc1_ucm_relax_model                  4
% 1.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.25/0.99  --bmc1_ucm_layered_model                none
% 1.25/0.99  --bmc1_ucm_max_lemma_size               10
% 1.25/0.99  
% 1.25/0.99  ------ AIG Options
% 1.25/0.99  
% 1.25/0.99  --aig_mode                              false
% 1.25/0.99  
% 1.25/0.99  ------ Instantiation Options
% 1.25/0.99  
% 1.25/0.99  --instantiation_flag                    true
% 1.25/0.99  --inst_sos_flag                         false
% 1.25/0.99  --inst_sos_phase                        true
% 1.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.25/0.99  --inst_lit_sel_side                     none
% 1.25/0.99  --inst_solver_per_active                1400
% 1.25/0.99  --inst_solver_calls_frac                1.
% 1.25/0.99  --inst_passive_queue_type               priority_queues
% 1.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.25/0.99  --inst_passive_queues_freq              [25;2]
% 1.25/0.99  --inst_dismatching                      true
% 1.25/0.99  --inst_eager_unprocessed_to_passive     true
% 1.25/0.99  --inst_prop_sim_given                   true
% 1.25/0.99  --inst_prop_sim_new                     false
% 1.25/0.99  --inst_subs_new                         false
% 1.25/0.99  --inst_eq_res_simp                      false
% 1.25/0.99  --inst_subs_given                       false
% 1.25/0.99  --inst_orphan_elimination               true
% 1.25/0.99  --inst_learning_loop_flag               true
% 1.25/0.99  --inst_learning_start                   3000
% 1.25/0.99  --inst_learning_factor                  2
% 1.25/0.99  --inst_start_prop_sim_after_learn       3
% 1.25/0.99  --inst_sel_renew                        solver
% 1.25/0.99  --inst_lit_activity_flag                true
% 1.25/0.99  --inst_restr_to_given                   false
% 1.25/0.99  --inst_activity_threshold               500
% 1.25/0.99  --inst_out_proof                        true
% 1.25/0.99  
% 1.25/0.99  ------ Resolution Options
% 1.25/0.99  
% 1.25/0.99  --resolution_flag                       false
% 1.25/0.99  --res_lit_sel                           adaptive
% 1.25/0.99  --res_lit_sel_side                      none
% 1.25/0.99  --res_ordering                          kbo
% 1.25/0.99  --res_to_prop_solver                    active
% 1.25/0.99  --res_prop_simpl_new                    false
% 1.25/0.99  --res_prop_simpl_given                  true
% 1.25/0.99  --res_passive_queue_type                priority_queues
% 1.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.25/0.99  --res_passive_queues_freq               [15;5]
% 1.25/0.99  --res_forward_subs                      full
% 1.25/0.99  --res_backward_subs                     full
% 1.25/0.99  --res_forward_subs_resolution           true
% 1.25/0.99  --res_backward_subs_resolution          true
% 1.25/0.99  --res_orphan_elimination                true
% 1.25/0.99  --res_time_limit                        2.
% 1.25/0.99  --res_out_proof                         true
% 1.25/0.99  
% 1.25/0.99  ------ Superposition Options
% 1.25/0.99  
% 1.25/0.99  --superposition_flag                    true
% 1.25/0.99  --sup_passive_queue_type                priority_queues
% 1.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.25/0.99  --demod_completeness_check              fast
% 1.25/0.99  --demod_use_ground                      true
% 1.25/0.99  --sup_to_prop_solver                    passive
% 1.25/0.99  --sup_prop_simpl_new                    true
% 1.25/0.99  --sup_prop_simpl_given                  true
% 1.25/0.99  --sup_fun_splitting                     false
% 1.25/0.99  --sup_smt_interval                      50000
% 1.25/0.99  
% 1.25/0.99  ------ Superposition Simplification Setup
% 1.25/0.99  
% 1.25/0.99  --sup_indices_passive                   []
% 1.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_full_bw                           [BwDemod]
% 1.25/0.99  --sup_immed_triv                        [TrivRules]
% 1.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_immed_bw_main                     []
% 1.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.25/0.99  
% 1.25/0.99  ------ Combination Options
% 1.25/0.99  
% 1.25/0.99  --comb_res_mult                         3
% 1.25/0.99  --comb_sup_mult                         2
% 1.25/0.99  --comb_inst_mult                        10
% 1.25/0.99  
% 1.25/0.99  ------ Debug Options
% 1.25/0.99  
% 1.25/0.99  --dbg_backtrace                         false
% 1.25/0.99  --dbg_dump_prop_clauses                 false
% 1.25/0.99  --dbg_dump_prop_clauses_file            -
% 1.25/0.99  --dbg_out_stat                          false
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  ------ Proving...
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  % SZS status Theorem for theBenchmark.p
% 1.25/0.99  
% 1.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.25/0.99  
% 1.25/0.99  fof(f5,axiom,(
% 1.25/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f14,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.25/0.99    inference(ennf_transformation,[],[f5])).
% 1.25/0.99  
% 1.25/0.99  fof(f15,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(flattening,[],[f14])).
% 1.25/0.99  
% 1.25/0.99  fof(f25,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(nnf_transformation,[],[f15])).
% 1.25/0.99  
% 1.25/0.99  fof(f26,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(rectify,[],[f25])).
% 1.25/0.99  
% 1.25/0.99  fof(f27,plain,(
% 1.25/0.99    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.25/0.99    introduced(choice_axiom,[])).
% 1.25/0.99  
% 1.25/0.99  fof(f28,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.25/0.99  
% 1.25/0.99  fof(f42,plain,(
% 1.25/0.99    ( ! [X2,X0,X1] : (k4_orders_2(X0,X1) = X2 | m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f28])).
% 1.25/0.99  
% 1.25/0.99  fof(f9,conjecture,(
% 1.25/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f10,negated_conjecture,(
% 1.25/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.25/0.99    inference(negated_conjecture,[],[f9])).
% 1.25/0.99  
% 1.25/0.99  fof(f21,plain,(
% 1.25/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.25/0.99    inference(ennf_transformation,[],[f10])).
% 1.25/0.99  
% 1.25/0.99  fof(f22,plain,(
% 1.25/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.25/0.99    inference(flattening,[],[f21])).
% 1.25/0.99  
% 1.25/0.99  fof(f32,plain,(
% 1.25/0.99    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))))) )),
% 1.25/0.99    introduced(choice_axiom,[])).
% 1.25/0.99  
% 1.25/0.99  fof(f31,plain,(
% 1.25/0.99    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.25/0.99    introduced(choice_axiom,[])).
% 1.25/0.99  
% 1.25/0.99  fof(f33,plain,(
% 1.25/0.99    (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f32,f31])).
% 1.25/0.99  
% 1.25/0.99  fof(f54,plain,(
% 1.25/0.99    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f53,plain,(
% 1.25/0.99    l1_orders_2(sK3)),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f49,plain,(
% 1.25/0.99    ~v2_struct_0(sK3)),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f50,plain,(
% 1.25/0.99    v3_orders_2(sK3)),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f51,plain,(
% 1.25/0.99    v4_orders_2(sK3)),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f52,plain,(
% 1.25/0.99    v5_orders_2(sK3)),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f41,plain,(
% 1.25/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f28])).
% 1.25/0.99  
% 1.25/0.99  fof(f56,plain,(
% 1.25/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(equality_resolution,[],[f41])).
% 1.25/0.99  
% 1.25/0.99  fof(f55,plain,(
% 1.25/0.99    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))),
% 1.25/0.99    inference(cnf_transformation,[],[f33])).
% 1.25/0.99  
% 1.25/0.99  fof(f8,axiom,(
% 1.25/0.99    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f11,plain,(
% 1.25/0.99    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.25/0.99    inference(rectify,[],[f8])).
% 1.25/0.99  
% 1.25/0.99  fof(f20,plain,(
% 1.25/0.99    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.25/0.99    inference(ennf_transformation,[],[f11])).
% 1.25/0.99  
% 1.25/0.99  fof(f29,plain,(
% 1.25/0.99    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 1.25/0.99    introduced(choice_axiom,[])).
% 1.25/0.99  
% 1.25/0.99  fof(f30,plain,(
% 1.25/0.99    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f29])).
% 1.25/0.99  
% 1.25/0.99  fof(f46,plain,(
% 1.25/0.99    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.25/0.99    inference(cnf_transformation,[],[f30])).
% 1.25/0.99  
% 1.25/0.99  fof(f1,axiom,(
% 1.25/0.99    v1_xboole_0(k1_xboole_0)),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f34,plain,(
% 1.25/0.99    v1_xboole_0(k1_xboole_0)),
% 1.25/0.99    inference(cnf_transformation,[],[f1])).
% 1.25/0.99  
% 1.25/0.99  fof(f6,axiom,(
% 1.25/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f16,plain,(
% 1.25/0.99    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.25/0.99    inference(ennf_transformation,[],[f6])).
% 1.25/0.99  
% 1.25/0.99  fof(f17,plain,(
% 1.25/0.99    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(flattening,[],[f16])).
% 1.25/0.99  
% 1.25/0.99  fof(f44,plain,(
% 1.25/0.99    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f17])).
% 1.25/0.99  
% 1.25/0.99  fof(f43,plain,(
% 1.25/0.99    ( ! [X2,X0,X1] : (k4_orders_2(X0,X1) = X2 | ~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f28])).
% 1.25/0.99  
% 1.25/0.99  fof(f2,axiom,(
% 1.25/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f35,plain,(
% 1.25/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f2])).
% 1.25/0.99  
% 1.25/0.99  fof(f3,axiom,(
% 1.25/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f12,plain,(
% 1.25/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.25/0.99    inference(ennf_transformation,[],[f3])).
% 1.25/0.99  
% 1.25/0.99  fof(f36,plain,(
% 1.25/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f12])).
% 1.25/0.99  
% 1.25/0.99  fof(f7,axiom,(
% 1.25/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.25/0.99  
% 1.25/0.99  fof(f18,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.25/0.99    inference(ennf_transformation,[],[f7])).
% 1.25/0.99  
% 1.25/0.99  fof(f19,plain,(
% 1.25/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.99    inference(flattening,[],[f18])).
% 1.25/0.99  
% 1.25/0.99  fof(f45,plain,(
% 1.25/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.25/0.99    inference(cnf_transformation,[],[f19])).
% 1.25/0.99  
% 1.25/0.99  cnf(c_7,plain,
% 1.25/0.99      ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.25/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.25/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,X1) = X2 ),
% 1.25/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_16,negated_conjecture,
% 1.25/0.99      ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
% 1.25/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_273,plain,
% 1.25/0.99      ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.25/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,X1) = X2
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK4 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_274,plain,
% 1.25/0.99      ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.25/0.99      | r2_hidden(sK1(X0,sK4,X1),X1)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) = X1
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_273]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_17,negated_conjecture,
% 1.25/0.99      ( l1_orders_2(sK3) ),
% 1.25/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_546,plain,
% 1.25/0.99      ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.25/0.99      | r2_hidden(sK1(X0,sK4,X1),X1)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) = X1
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK3 != X0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_274,c_17]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_547,plain,
% 1.25/0.99      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | v2_struct_0(sK3)
% 1.25/0.99      | ~ v3_orders_2(sK3)
% 1.25/0.99      | ~ v4_orders_2(sK3)
% 1.25/0.99      | ~ v5_orders_2(sK3)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_21,negated_conjecture,
% 1.25/0.99      ( ~ v2_struct_0(sK3) ),
% 1.25/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_20,negated_conjecture,
% 1.25/0.99      ( v3_orders_2(sK3) ),
% 1.25/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_19,negated_conjecture,
% 1.25/0.99      ( v4_orders_2(sK3) ),
% 1.25/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_18,negated_conjecture,
% 1.25/0.99      ( v5_orders_2(sK3) ),
% 1.25/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_551,plain,
% 1.25/0.99      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(global_propositional_subsumption,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_547,c_21,c_20,c_19,c_18]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1136,plain,
% 1.25/0.99      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0 ),
% 1.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_551]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1957,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
% 1.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_8,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.25/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1) ),
% 1.25/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_399,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK4 != X2 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_400,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,sK4)
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_570,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,sK4)
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK3 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_400,c_17]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_571,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.25/0.99      | v2_struct_0(sK3)
% 1.25/0.99      | ~ v3_orders_2(sK3)
% 1.25/0.99      | ~ v4_orders_2(sK3)
% 1.25/0.99      | ~ v5_orders_2(sK3)
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_575,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(global_propositional_subsumption,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_571,c_21,c_20,c_19,c_18]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1134,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_575]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1167,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.25/0.99      inference(prop_impl,[status(thm)],[c_1134]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1958,plain,
% 1.25/0.99      ( m2_orders_2(X0,sK3,sK4) != iProver_top
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
% 1.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_15,negated_conjecture,
% 1.25/0.99      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
% 1.25/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_14,plain,
% 1.25/0.99      ( ~ r2_hidden(X0,X1)
% 1.25/0.99      | k3_tarski(X1) != k1_xboole_0
% 1.25/0.99      | k1_xboole_0 = X0 ),
% 1.25/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1962,plain,
% 1.25/0.99      ( k3_tarski(X0) != k1_xboole_0
% 1.25/0.99      | k1_xboole_0 = X1
% 1.25/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 1.25/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2573,plain,
% 1.25/0.99      ( k1_xboole_0 = X0
% 1.25/0.99      | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
% 1.25/0.99      inference(superposition,[status(thm)],[c_15,c_1962]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2659,plain,
% 1.25/0.99      ( k1_xboole_0 = X0 | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 1.25/0.99      inference(superposition,[status(thm)],[c_1958,c_2573]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2681,plain,
% 1.25/0.99      ( sK1(sK3,sK4,X0) = k1_xboole_0
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
% 1.25/0.99      inference(superposition,[status(thm)],[c_1957,c_2659]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2693,plain,
% 1.25/0.99      ( sK1(sK3,sK4,k1_xboole_0) = k1_xboole_0
% 1.25/0.99      | k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_2681]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1658,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.25/0.99      | m2_orders_2(X3,X4,X5)
% 1.25/0.99      | X3 != X0
% 1.25/0.99      | X4 != X1
% 1.25/0.99      | X5 != X2 ),
% 1.25/0.99      theory(equality) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2071,plain,
% 1.25/0.99      ( m2_orders_2(X0,X1,X2)
% 1.25/0.99      | ~ m2_orders_2(sK1(sK3,sK4,X3),sK3,sK4)
% 1.25/0.99      | X0 != sK1(sK3,sK4,X3)
% 1.25/0.99      | X2 != sK4
% 1.25/0.99      | X1 != sK3 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1658]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2410,plain,
% 1.25/0.99      ( m2_orders_2(X0,sK3,X1)
% 1.25/0.99      | ~ m2_orders_2(sK1(sK3,sK4,X2),sK3,sK4)
% 1.25/0.99      | X0 != sK1(sK3,sK4,X2)
% 1.25/0.99      | X1 != sK4
% 1.25/0.99      | sK3 != sK3 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_2071]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2589,plain,
% 1.25/0.99      ( m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | ~ m2_orders_2(sK1(sK3,sK4,X1),sK3,sK4)
% 1.25/0.99      | X0 != sK1(sK3,sK4,X1)
% 1.25/0.99      | sK4 != sK4
% 1.25/0.99      | sK3 != sK3 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_2410]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2591,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
% 1.25/0.99      | m2_orders_2(k1_xboole_0,sK3,sK4)
% 1.25/0.99      | sK4 != sK4
% 1.25/0.99      | sK3 != sK3
% 1.25/0.99      | k1_xboole_0 != sK1(sK3,sK4,k1_xboole_0) ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_2589]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1653,plain,( X0 = X0 ),theory(equality) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2411,plain,
% 1.25/0.99      ( sK3 = sK3 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1653]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2192,plain,
% 1.25/0.99      ( sK4 = sK4 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1653]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1654,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2123,plain,
% 1.25/0.99      ( X0 != X1 | X0 = sK1(sK3,sK4,X2) | sK1(sK3,sK4,X2) != X1 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1654]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2124,plain,
% 1.25/0.99      ( sK1(sK3,sK4,k1_xboole_0) != k1_xboole_0
% 1.25/0.99      | k1_xboole_0 = sK1(sK3,sK4,k1_xboole_0)
% 1.25/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1670,plain,
% 1.25/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1653]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_0,plain,
% 1.25/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.25/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_10,plain,
% 1.25/0.99      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 1.25/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_239,plain,
% 1.25/0.99      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | k4_orders_2(X1,X0) != k1_xboole_0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_429,plain,
% 1.25/0.99      ( v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,X1) != k1_xboole_0
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK4 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_239,c_16]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_430,plain,
% 1.25/0.99      ( v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) != k1_xboole_0
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_511,plain,
% 1.25/0.99      ( v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) != k1_xboole_0
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK3 != X0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_430,c_17]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_512,plain,
% 1.25/0.99      ( v2_struct_0(sK3)
% 1.25/0.99      | ~ v3_orders_2(sK3)
% 1.25/0.99      | ~ v4_orders_2(sK3)
% 1.25/0.99      | ~ v5_orders_2(sK3)
% 1.25/0.99      | k4_orders_2(sK3,sK4) != k1_xboole_0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_514,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) != k1_xboole_0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(global_propositional_subsumption,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_512,c_21,c_20,c_19,c_18]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1142,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) != k1_xboole_0 ),
% 1.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_514]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_6,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.25/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.25/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,X1) = X2 ),
% 1.25/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_306,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.25/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,X1) = X2
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK4 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_307,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.25/0.99      | ~ r2_hidden(sK1(X0,sK4,X1),X1)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | ~ l1_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) = X1
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_522,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.25/0.99      | ~ r2_hidden(sK1(X0,sK4,X1),X1)
% 1.25/0.99      | v2_struct_0(X0)
% 1.25/0.99      | ~ v3_orders_2(X0)
% 1.25/0.99      | ~ v4_orders_2(X0)
% 1.25/0.99      | ~ v5_orders_2(X0)
% 1.25/0.99      | k4_orders_2(X0,sK4) = X1
% 1.25/0.99      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK3 != X0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_307,c_17]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_523,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | v2_struct_0(sK3)
% 1.25/0.99      | ~ v3_orders_2(sK3)
% 1.25/0.99      | ~ v4_orders_2(sK3)
% 1.25/0.99      | ~ v5_orders_2(sK3)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_527,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(global_propositional_subsumption,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_523,c_21,c_20,c_19,c_18]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1138,plain,
% 1.25/0.99      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0 ),
% 1.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_527]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1139,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) != iProver_top
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,X0),X0) != iProver_top ),
% 1.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1141,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.25/0.99      | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) != iProver_top
% 1.25/0.99      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 1.25/0.99      inference(instantiation,[status(thm)],[c_1139]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1,plain,
% 1.25/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 1.25/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_2,plain,
% 1.25/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.25/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_228,plain,
% 1.25/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_229,plain,
% 1.25/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_228]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_11,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.25/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.25/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1) ),
% 1.25/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_339,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.25/0.99      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK4 != X2 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_340,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,sK4)
% 1.25/0.99      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | ~ l1_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_612,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,X1,sK4)
% 1.25/0.99      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.25/0.99      | v2_struct_0(X1)
% 1.25/0.99      | ~ v3_orders_2(X1)
% 1.25/0.99      | ~ v4_orders_2(X1)
% 1.25/0.99      | ~ v5_orders_2(X1)
% 1.25/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | sK3 != X1 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_340,c_17]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_613,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.25/0.99      | v2_struct_0(sK3)
% 1.25/0.99      | ~ v3_orders_2(sK3)
% 1.25/0.99      | ~ v4_orders_2(sK3)
% 1.25/0.99      | ~ v5_orders_2(sK3)
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_612]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_617,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.25/0.99      inference(global_propositional_subsumption,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_613,c_21,c_20,c_19,c_18]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1013,plain,
% 1.25/0.99      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.25/0.99      | k1_funct_1(sK4,u1_struct_0(sK3)) != X1
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | k1_xboole_0 != X0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_229,c_617]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_1014,plain,
% 1.25/0.99      ( ~ m2_orders_2(k1_xboole_0,sK3,sK4) ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_1013]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_991,plain,
% 1.25/0.99      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.25/0.99      | sK1(sK3,sK4,X0) != X1
% 1.25/0.99      | k4_orders_2(sK3,sK4) = X0
% 1.25/0.99      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
% 1.25/0.99      | k1_xboole_0 != X0 ),
% 1.25/0.99      inference(resolution_lifted,[status(thm)],[c_229,c_551]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_992,plain,
% 1.25/0.99      ( m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
% 1.25/0.99      | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
% 1.25/0.99      inference(unflattening,[status(thm)],[c_991]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(c_993,plain,
% 1.25/0.99      ( k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.25/0.99      | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) = iProver_top ),
% 1.25/0.99      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 1.25/0.99  
% 1.25/0.99  cnf(contradiction,plain,
% 1.25/0.99      ( $false ),
% 1.25/0.99      inference(minisat,
% 1.25/0.99                [status(thm)],
% 1.25/0.99                [c_2693,c_2591,c_2411,c_2192,c_2124,c_1670,c_1142,c_1141,
% 1.25/0.99                 c_1014,c_993,c_992]) ).
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.25/0.99  
% 1.25/0.99  ------                               Statistics
% 1.25/0.99  
% 1.25/0.99  ------ General
% 1.25/0.99  
% 1.25/0.99  abstr_ref_over_cycles:                  0
% 1.25/0.99  abstr_ref_under_cycles:                 0
% 1.25/0.99  gc_basic_clause_elim:                   0
% 1.25/0.99  forced_gc_time:                         0
% 1.25/0.99  parsing_time:                           0.017
% 1.25/0.99  unif_index_cands_time:                  0.
% 1.25/0.99  unif_index_add_time:                    0.
% 1.25/0.99  orderings_time:                         0.
% 1.25/0.99  out_proof_time:                         0.012
% 1.25/0.99  total_time:                             0.108
% 1.25/0.99  num_of_symbols:                         53
% 1.25/0.99  num_of_terms:                           1486
% 1.25/0.99  
% 1.25/0.99  ------ Preprocessing
% 1.25/0.99  
% 1.25/0.99  num_of_splits:                          0
% 1.25/0.99  num_of_split_atoms:                     0
% 1.25/0.99  num_of_reused_defs:                     0
% 1.25/0.99  num_eq_ax_congr_red:                    27
% 1.25/0.99  num_of_sem_filtered_clauses:            1
% 1.25/0.99  num_of_subtypes:                        0
% 1.25/0.99  monotx_restored_types:                  0
% 1.25/0.99  sat_num_of_epr_types:                   0
% 1.25/0.99  sat_num_of_non_cyclic_types:            0
% 1.25/0.99  sat_guarded_non_collapsed_types:        0
% 1.25/0.99  num_pure_diseq_elim:                    0
% 1.25/0.99  simp_replaced_by:                       0
% 1.25/0.99  res_preprocessed:                       83
% 1.25/0.99  prep_upred:                             0
% 1.25/0.99  prep_unflattend:                        124
% 1.25/0.99  smt_new_axioms:                         0
% 1.25/0.99  pred_elim_cands:                        2
% 1.25/0.99  pred_elim:                              8
% 1.25/0.99  pred_elim_cl:                           8
% 1.25/0.99  pred_elim_cycles:                       12
% 1.25/0.99  merged_defs:                            6
% 1.25/0.99  merged_defs_ncl:                        0
% 1.25/0.99  bin_hyper_res:                          6
% 1.25/0.99  prep_cycles:                            4
% 1.25/0.99  pred_elim_time:                         0.023
% 1.25/0.99  splitting_time:                         0.
% 1.25/0.99  sem_filter_time:                        0.
% 1.25/0.99  monotx_time:                            0.
% 1.25/0.99  subtype_inf_time:                       0.
% 1.25/0.99  
% 1.25/0.99  ------ Problem properties
% 1.25/0.99  
% 1.25/0.99  clauses:                                14
% 1.25/0.99  conjectures:                            1
% 1.25/0.99  epr:                                    1
% 1.25/0.99  horn:                                   11
% 1.25/0.99  ground:                                 2
% 1.25/0.99  unary:                                  3
% 1.25/0.99  binary:                                 6
% 1.25/0.99  lits:                                   30
% 1.25/0.99  lits_eq:                                14
% 1.25/0.99  fd_pure:                                0
% 1.25/0.99  fd_pseudo:                              0
% 1.25/0.99  fd_cond:                                6
% 1.25/0.99  fd_pseudo_cond:                         0
% 1.25/0.99  ac_symbols:                             0
% 1.25/0.99  
% 1.25/0.99  ------ Propositional Solver
% 1.25/0.99  
% 1.25/0.99  prop_solver_calls:                      26
% 1.25/0.99  prop_fast_solver_calls:                 746
% 1.25/0.99  smt_solver_calls:                       0
% 1.25/0.99  smt_fast_solver_calls:                  0
% 1.25/0.99  prop_num_of_clauses:                    532
% 1.25/0.99  prop_preprocess_simplified:             2792
% 1.25/0.99  prop_fo_subsumed:                       26
% 1.25/0.99  prop_solver_time:                       0.
% 1.25/0.99  smt_solver_time:                        0.
% 1.25/0.99  smt_fast_solver_time:                   0.
% 1.25/0.99  prop_fast_solver_time:                  0.
% 1.25/0.99  prop_unsat_core_time:                   0.
% 1.25/0.99  
% 1.25/0.99  ------ QBF
% 1.25/0.99  
% 1.25/0.99  qbf_q_res:                              0
% 1.25/0.99  qbf_num_tautologies:                    0
% 1.25/0.99  qbf_prep_cycles:                        0
% 1.25/0.99  
% 1.25/0.99  ------ BMC1
% 1.25/0.99  
% 1.25/0.99  bmc1_current_bound:                     -1
% 1.25/0.99  bmc1_last_solved_bound:                 -1
% 1.25/0.99  bmc1_unsat_core_size:                   -1
% 1.25/0.99  bmc1_unsat_core_parents_size:           -1
% 1.25/0.99  bmc1_merge_next_fun:                    0
% 1.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.25/0.99  
% 1.25/0.99  ------ Instantiation
% 1.25/0.99  
% 1.25/0.99  inst_num_of_clauses:                    124
% 1.25/0.99  inst_num_in_passive:                    28
% 1.25/0.99  inst_num_in_active:                     74
% 1.25/0.99  inst_num_in_unprocessed:                22
% 1.25/0.99  inst_num_of_loops:                      90
% 1.25/0.99  inst_num_of_learning_restarts:          0
% 1.25/0.99  inst_num_moves_active_passive:          13
% 1.25/0.99  inst_lit_activity:                      0
% 1.25/0.99  inst_lit_activity_moves:                0
% 1.25/0.99  inst_num_tautologies:                   0
% 1.25/0.99  inst_num_prop_implied:                  0
% 1.25/0.99  inst_num_existing_simplified:           0
% 1.25/0.99  inst_num_eq_res_simplified:             0
% 1.25/0.99  inst_num_child_elim:                    0
% 1.25/0.99  inst_num_of_dismatching_blockings:      5
% 1.25/0.99  inst_num_of_non_proper_insts:           79
% 1.25/0.99  inst_num_of_duplicates:                 0
% 1.25/0.99  inst_inst_num_from_inst_to_res:         0
% 1.25/0.99  inst_dismatching_checking_time:         0.
% 1.25/0.99  
% 1.25/0.99  ------ Resolution
% 1.25/0.99  
% 1.25/0.99  res_num_of_clauses:                     0
% 1.25/0.99  res_num_in_passive:                     0
% 1.25/0.99  res_num_in_active:                      0
% 1.25/0.99  res_num_of_loops:                       87
% 1.25/0.99  res_forward_subset_subsumed:            7
% 1.25/0.99  res_backward_subset_subsumed:           0
% 1.25/0.99  res_forward_subsumed:                   0
% 1.25/0.99  res_backward_subsumed:                  0
% 1.25/0.99  res_forward_subsumption_resolution:     0
% 1.25/0.99  res_backward_subsumption_resolution:    0
% 1.25/0.99  res_clause_to_clause_subsumption:       93
% 1.25/0.99  res_orphan_elimination:                 0
% 1.25/0.99  res_tautology_del:                      34
% 1.25/0.99  res_num_eq_res_simplified:              6
% 1.25/0.99  res_num_sel_changes:                    0
% 1.25/0.99  res_moves_from_active_to_pass:          0
% 1.25/0.99  
% 1.25/0.99  ------ Superposition
% 1.25/0.99  
% 1.25/0.99  sup_time_total:                         0.
% 1.25/0.99  sup_time_generating:                    0.
% 1.25/0.99  sup_time_sim_full:                      0.
% 1.25/0.99  sup_time_sim_immed:                     0.
% 1.25/0.99  
% 1.25/0.99  sup_num_of_clauses:                     26
% 1.25/0.99  sup_num_in_active:                      18
% 1.25/0.99  sup_num_in_passive:                     8
% 1.25/0.99  sup_num_of_loops:                       17
% 1.25/0.99  sup_fw_superposition:                   17
% 1.25/0.99  sup_bw_superposition:                   4
% 1.25/0.99  sup_immediate_simplified:               4
% 1.25/0.99  sup_given_eliminated:                   0
% 1.25/0.99  comparisons_done:                       0
% 1.25/0.99  comparisons_avoided:                    0
% 1.25/0.99  
% 1.25/0.99  ------ Simplifications
% 1.25/0.99  
% 1.25/0.99  
% 1.25/0.99  sim_fw_subset_subsumed:                 1
% 1.25/0.99  sim_bw_subset_subsumed:                 0
% 1.25/0.99  sim_fw_subsumed:                        1
% 1.25/0.99  sim_bw_subsumed:                        0
% 1.25/0.99  sim_fw_subsumption_res:                 0
% 1.25/0.99  sim_bw_subsumption_res:                 0
% 1.25/0.99  sim_tautology_del:                      2
% 1.25/0.99  sim_eq_tautology_del:                   5
% 1.25/0.99  sim_eq_res_simp:                        0
% 1.25/0.99  sim_fw_demodulated:                     2
% 1.25/0.99  sim_bw_demodulated:                     0
% 1.25/0.99  sim_light_normalised:                   0
% 1.25/0.99  sim_joinable_taut:                      0
% 1.25/0.99  sim_joinable_simp:                      0
% 1.25/0.99  sim_ac_normalised:                      0
% 1.25/0.99  sim_smt_subsumption:                    0
% 1.25/0.99  
%------------------------------------------------------------------------------
