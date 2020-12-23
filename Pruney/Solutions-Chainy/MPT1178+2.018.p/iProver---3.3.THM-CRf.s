%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:00 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 366 expanded)
%              Number of clauses        :   69 ( 101 expanded)
%              Number of leaves         :   18 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :  508 (1951 expanded)
%              Number of equality atoms :  104 ( 343 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f29])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3))
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36,f35])).

fof(f60,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f49,plain,(
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

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

cnf(c_1461,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1959,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
    | X0 != sK0(k4_orders_2(sK2,sK3))
    | X2 != sK3
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_2592,plain,
    ( m2_orders_2(X0,X1,sK3)
    | ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
    | X0 != sK0(k4_orders_2(sK2,sK3))
    | X1 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_4398,plain,
    ( ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
    | m2_orders_2(k1_xboole_0,X0,sK3)
    | X0 != sK2
    | sK3 != sK3
    | k1_xboole_0 != sK0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_4422,plain,
    ( ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
    | m2_orders_2(k1_xboole_0,sK2,sK3)
    | sK3 != sK3
    | sK2 != sK2
    | k1_xboole_0 != sK0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4398])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_301,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_302,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_15,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_506,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,X1))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_507,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK3))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_622,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK3))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_507,c_19])).

cnf(c_623,plain,
    ( v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v1_xboole_0(k4_orders_2(sK2,sK3))
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_625,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK2,sK3))
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_23,c_22,c_21,c_20])).

cnf(c_772,plain,
    ( r2_hidden(sK0(X0),X0)
    | k4_orders_2(sK2,sK3) != X0
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(resolution_lifted,[status(thm)],[c_302,c_625])).

cnf(c_773,plain,
    ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_1826,plain,
    ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1830,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1828,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2759,plain,
    ( r1_tarski(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | r1_tarski(k3_tarski(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1828])).

cnf(c_3023,plain,
    ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | r1_tarski(k3_tarski(k1_tarski(X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_2759])).

cnf(c_6,plain,
    ( k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3026,plain,
    ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3023,c_6])).

cnf(c_3203,plain,
    ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1826,c_3026])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2702,plain,
    ( r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2705,plain,
    ( r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2702])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2077,plain,
    ( ~ r1_tarski(X0,sK0(k4_orders_2(sK2,sK3)))
    | ~ r1_tarski(sK0(k4_orders_2(sK2,sK3)),X0)
    | X0 = sK0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2701,plain,
    ( ~ r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3)))
    | k1_xboole_0 = sK0(k4_orders_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_2703,plain,
    ( k1_xboole_0 = sK0(k4_orders_2(sK2,sK3))
    | r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2701])).

cnf(c_1831,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_416,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_417,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_726,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_19])).

cnf(c_727,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_23,c_22,c_21,c_20])).

cnf(c_1072,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_731])).

cnf(c_1825,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1827,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2204,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r1_tarski(X0,k1_funct_1(sK3,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1827])).

cnf(c_2441,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_2204])).

cnf(c_2452,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2441])).

cnf(c_1453,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2167,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1453])).

cnf(c_14,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_446,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_447,plain,
    ( m2_orders_2(X0,X1,sK3)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_705,plain,
    ( m2_orders_2(X0,X1,sK3)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_19])).

cnf(c_706,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_710,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_23,c_22,c_21,c_20])).

cnf(c_989,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | k4_orders_2(sK2,sK3) != k4_orders_2(sK2,sK3)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2))
    | sK0(k4_orders_2(sK2,sK3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_773,c_710])).

cnf(c_990,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_75,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_71,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4422,c_3203,c_2705,c_2703,c_2452,c_2167,c_990,c_75,c_71])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.88/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/1.03  
% 2.88/1.03  ------  iProver source info
% 2.88/1.03  
% 2.88/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.88/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/1.03  git: non_committed_changes: false
% 2.88/1.03  git: last_make_outside_of_git: false
% 2.88/1.03  
% 2.88/1.03  ------ 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options
% 2.88/1.03  
% 2.88/1.03  --out_options                           all
% 2.88/1.03  --tptp_safe_out                         true
% 2.88/1.03  --problem_path                          ""
% 2.88/1.03  --include_path                          ""
% 2.88/1.03  --clausifier                            res/vclausify_rel
% 2.88/1.03  --clausifier_options                    --mode clausify
% 2.88/1.03  --stdin                                 false
% 2.88/1.03  --stats_out                             all
% 2.88/1.03  
% 2.88/1.03  ------ General Options
% 2.88/1.03  
% 2.88/1.03  --fof                                   false
% 2.88/1.03  --time_out_real                         305.
% 2.88/1.03  --time_out_virtual                      -1.
% 2.88/1.03  --symbol_type_check                     false
% 2.88/1.03  --clausify_out                          false
% 2.88/1.03  --sig_cnt_out                           false
% 2.88/1.03  --trig_cnt_out                          false
% 2.88/1.03  --trig_cnt_out_tolerance                1.
% 2.88/1.03  --trig_cnt_out_sk_spl                   false
% 2.88/1.03  --abstr_cl_out                          false
% 2.88/1.03  
% 2.88/1.03  ------ Global Options
% 2.88/1.03  
% 2.88/1.03  --schedule                              default
% 2.88/1.03  --add_important_lit                     false
% 2.88/1.03  --prop_solver_per_cl                    1000
% 2.88/1.03  --min_unsat_core                        false
% 2.88/1.03  --soft_assumptions                      false
% 2.88/1.03  --soft_lemma_size                       3
% 2.88/1.03  --prop_impl_unit_size                   0
% 2.88/1.03  --prop_impl_unit                        []
% 2.88/1.03  --share_sel_clauses                     true
% 2.88/1.03  --reset_solvers                         false
% 2.88/1.03  --bc_imp_inh                            [conj_cone]
% 2.88/1.03  --conj_cone_tolerance                   3.
% 2.88/1.03  --extra_neg_conj                        none
% 2.88/1.03  --large_theory_mode                     true
% 2.88/1.03  --prolific_symb_bound                   200
% 2.88/1.03  --lt_threshold                          2000
% 2.88/1.03  --clause_weak_htbl                      true
% 2.88/1.03  --gc_record_bc_elim                     false
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing Options
% 2.88/1.03  
% 2.88/1.03  --preprocessing_flag                    true
% 2.88/1.03  --time_out_prep_mult                    0.1
% 2.88/1.03  --splitting_mode                        input
% 2.88/1.03  --splitting_grd                         true
% 2.88/1.03  --splitting_cvd                         false
% 2.88/1.03  --splitting_cvd_svl                     false
% 2.88/1.03  --splitting_nvd                         32
% 2.88/1.03  --sub_typing                            true
% 2.88/1.03  --prep_gs_sim                           true
% 2.88/1.03  --prep_unflatten                        true
% 2.88/1.03  --prep_res_sim                          true
% 2.88/1.03  --prep_upred                            true
% 2.88/1.03  --prep_sem_filter                       exhaustive
% 2.88/1.03  --prep_sem_filter_out                   false
% 2.88/1.03  --pred_elim                             true
% 2.88/1.03  --res_sim_input                         true
% 2.88/1.03  --eq_ax_congr_red                       true
% 2.88/1.03  --pure_diseq_elim                       true
% 2.88/1.03  --brand_transform                       false
% 2.88/1.03  --non_eq_to_eq                          false
% 2.88/1.03  --prep_def_merge                        true
% 2.88/1.03  --prep_def_merge_prop_impl              false
% 2.88/1.03  --prep_def_merge_mbd                    true
% 2.88/1.03  --prep_def_merge_tr_red                 false
% 2.88/1.03  --prep_def_merge_tr_cl                  false
% 2.88/1.03  --smt_preprocessing                     true
% 2.88/1.03  --smt_ac_axioms                         fast
% 2.88/1.03  --preprocessed_out                      false
% 2.88/1.03  --preprocessed_stats                    false
% 2.88/1.03  
% 2.88/1.03  ------ Abstraction refinement Options
% 2.88/1.03  
% 2.88/1.03  --abstr_ref                             []
% 2.88/1.03  --abstr_ref_prep                        false
% 2.88/1.03  --abstr_ref_until_sat                   false
% 2.88/1.03  --abstr_ref_sig_restrict                funpre
% 2.88/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.03  --abstr_ref_under                       []
% 2.88/1.03  
% 2.88/1.03  ------ SAT Options
% 2.88/1.03  
% 2.88/1.03  --sat_mode                              false
% 2.88/1.03  --sat_fm_restart_options                ""
% 2.88/1.03  --sat_gr_def                            false
% 2.88/1.03  --sat_epr_types                         true
% 2.88/1.03  --sat_non_cyclic_types                  false
% 2.88/1.03  --sat_finite_models                     false
% 2.88/1.03  --sat_fm_lemmas                         false
% 2.88/1.03  --sat_fm_prep                           false
% 2.88/1.03  --sat_fm_uc_incr                        true
% 2.88/1.03  --sat_out_model                         small
% 2.88/1.03  --sat_out_clauses                       false
% 2.88/1.03  
% 2.88/1.03  ------ QBF Options
% 2.88/1.03  
% 2.88/1.03  --qbf_mode                              false
% 2.88/1.03  --qbf_elim_univ                         false
% 2.88/1.03  --qbf_dom_inst                          none
% 2.88/1.03  --qbf_dom_pre_inst                      false
% 2.88/1.03  --qbf_sk_in                             false
% 2.88/1.03  --qbf_pred_elim                         true
% 2.88/1.03  --qbf_split                             512
% 2.88/1.03  
% 2.88/1.03  ------ BMC1 Options
% 2.88/1.03  
% 2.88/1.03  --bmc1_incremental                      false
% 2.88/1.03  --bmc1_axioms                           reachable_all
% 2.88/1.03  --bmc1_min_bound                        0
% 2.88/1.03  --bmc1_max_bound                        -1
% 2.88/1.03  --bmc1_max_bound_default                -1
% 2.88/1.03  --bmc1_symbol_reachability              true
% 2.88/1.03  --bmc1_property_lemmas                  false
% 2.88/1.03  --bmc1_k_induction                      false
% 2.88/1.03  --bmc1_non_equiv_states                 false
% 2.88/1.03  --bmc1_deadlock                         false
% 2.88/1.03  --bmc1_ucm                              false
% 2.88/1.03  --bmc1_add_unsat_core                   none
% 2.88/1.03  --bmc1_unsat_core_children              false
% 2.88/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.03  --bmc1_out_stat                         full
% 2.88/1.03  --bmc1_ground_init                      false
% 2.88/1.03  --bmc1_pre_inst_next_state              false
% 2.88/1.03  --bmc1_pre_inst_state                   false
% 2.88/1.03  --bmc1_pre_inst_reach_state             false
% 2.88/1.03  --bmc1_out_unsat_core                   false
% 2.88/1.03  --bmc1_aig_witness_out                  false
% 2.88/1.03  --bmc1_verbose                          false
% 2.88/1.03  --bmc1_dump_clauses_tptp                false
% 2.88/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.03  --bmc1_dump_file                        -
% 2.88/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.03  --bmc1_ucm_extend_mode                  1
% 2.88/1.03  --bmc1_ucm_init_mode                    2
% 2.88/1.03  --bmc1_ucm_cone_mode                    none
% 2.88/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.03  --bmc1_ucm_relax_model                  4
% 2.88/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.03  --bmc1_ucm_layered_model                none
% 2.88/1.03  --bmc1_ucm_max_lemma_size               10
% 2.88/1.03  
% 2.88/1.03  ------ AIG Options
% 2.88/1.03  
% 2.88/1.03  --aig_mode                              false
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation Options
% 2.88/1.03  
% 2.88/1.03  --instantiation_flag                    true
% 2.88/1.03  --inst_sos_flag                         false
% 2.88/1.03  --inst_sos_phase                        true
% 2.88/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel_side                     num_symb
% 2.88/1.03  --inst_solver_per_active                1400
% 2.88/1.03  --inst_solver_calls_frac                1.
% 2.88/1.03  --inst_passive_queue_type               priority_queues
% 2.88/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.03  --inst_passive_queues_freq              [25;2]
% 2.88/1.03  --inst_dismatching                      true
% 2.88/1.03  --inst_eager_unprocessed_to_passive     true
% 2.88/1.03  --inst_prop_sim_given                   true
% 2.88/1.03  --inst_prop_sim_new                     false
% 2.88/1.03  --inst_subs_new                         false
% 2.88/1.03  --inst_eq_res_simp                      false
% 2.88/1.03  --inst_subs_given                       false
% 2.88/1.03  --inst_orphan_elimination               true
% 2.88/1.03  --inst_learning_loop_flag               true
% 2.88/1.03  --inst_learning_start                   3000
% 2.88/1.03  --inst_learning_factor                  2
% 2.88/1.03  --inst_start_prop_sim_after_learn       3
% 2.88/1.03  --inst_sel_renew                        solver
% 2.88/1.03  --inst_lit_activity_flag                true
% 2.88/1.03  --inst_restr_to_given                   false
% 2.88/1.03  --inst_activity_threshold               500
% 2.88/1.03  --inst_out_proof                        true
% 2.88/1.03  
% 2.88/1.03  ------ Resolution Options
% 2.88/1.03  
% 2.88/1.03  --resolution_flag                       true
% 2.88/1.03  --res_lit_sel                           adaptive
% 2.88/1.03  --res_lit_sel_side                      none
% 2.88/1.03  --res_ordering                          kbo
% 2.88/1.03  --res_to_prop_solver                    active
% 2.88/1.03  --res_prop_simpl_new                    false
% 2.88/1.03  --res_prop_simpl_given                  true
% 2.88/1.03  --res_passive_queue_type                priority_queues
% 2.88/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.03  --res_passive_queues_freq               [15;5]
% 2.88/1.03  --res_forward_subs                      full
% 2.88/1.03  --res_backward_subs                     full
% 2.88/1.03  --res_forward_subs_resolution           true
% 2.88/1.03  --res_backward_subs_resolution          true
% 2.88/1.03  --res_orphan_elimination                true
% 2.88/1.03  --res_time_limit                        2.
% 2.88/1.03  --res_out_proof                         true
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Options
% 2.88/1.03  
% 2.88/1.03  --superposition_flag                    true
% 2.88/1.03  --sup_passive_queue_type                priority_queues
% 2.88/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.03  --demod_completeness_check              fast
% 2.88/1.03  --demod_use_ground                      true
% 2.88/1.03  --sup_to_prop_solver                    passive
% 2.88/1.03  --sup_prop_simpl_new                    true
% 2.88/1.03  --sup_prop_simpl_given                  true
% 2.88/1.03  --sup_fun_splitting                     false
% 2.88/1.03  --sup_smt_interval                      50000
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Simplification Setup
% 2.88/1.03  
% 2.88/1.03  --sup_indices_passive                   []
% 2.88/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_full_bw                           [BwDemod]
% 2.88/1.03  --sup_immed_triv                        [TrivRules]
% 2.88/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_immed_bw_main                     []
% 2.88/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  
% 2.88/1.03  ------ Combination Options
% 2.88/1.03  
% 2.88/1.03  --comb_res_mult                         3
% 2.88/1.03  --comb_sup_mult                         2
% 2.88/1.03  --comb_inst_mult                        10
% 2.88/1.03  
% 2.88/1.03  ------ Debug Options
% 2.88/1.03  
% 2.88/1.03  --dbg_backtrace                         false
% 2.88/1.03  --dbg_dump_prop_clauses                 false
% 2.88/1.03  --dbg_dump_prop_clauses_file            -
% 2.88/1.03  --dbg_out_stat                          false
% 2.88/1.03  ------ Parsing...
% 2.88/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/1.03  ------ Proving...
% 2.88/1.03  ------ Problem Properties 
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  clauses                                 15
% 2.88/1.03  conjectures                             1
% 2.88/1.03  EPR                                     4
% 2.88/1.03  Horn                                    14
% 2.88/1.03  unary                                   5
% 2.88/1.03  binary                                  7
% 2.88/1.03  lits                                    28
% 2.88/1.03  lits eq                                 5
% 2.88/1.03  fd_pure                                 0
% 2.88/1.03  fd_pseudo                               0
% 2.88/1.03  fd_cond                                 2
% 2.88/1.03  fd_pseudo_cond                          1
% 2.88/1.03  AC symbols                              0
% 2.88/1.03  
% 2.88/1.03  ------ Schedule dynamic 5 is on 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  ------ 
% 2.88/1.03  Current options:
% 2.88/1.03  ------ 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options
% 2.88/1.03  
% 2.88/1.03  --out_options                           all
% 2.88/1.03  --tptp_safe_out                         true
% 2.88/1.03  --problem_path                          ""
% 2.88/1.03  --include_path                          ""
% 2.88/1.03  --clausifier                            res/vclausify_rel
% 2.88/1.03  --clausifier_options                    --mode clausify
% 2.88/1.03  --stdin                                 false
% 2.88/1.03  --stats_out                             all
% 2.88/1.03  
% 2.88/1.03  ------ General Options
% 2.88/1.03  
% 2.88/1.03  --fof                                   false
% 2.88/1.03  --time_out_real                         305.
% 2.88/1.03  --time_out_virtual                      -1.
% 2.88/1.03  --symbol_type_check                     false
% 2.88/1.03  --clausify_out                          false
% 2.88/1.03  --sig_cnt_out                           false
% 2.88/1.03  --trig_cnt_out                          false
% 2.88/1.03  --trig_cnt_out_tolerance                1.
% 2.88/1.03  --trig_cnt_out_sk_spl                   false
% 2.88/1.03  --abstr_cl_out                          false
% 2.88/1.03  
% 2.88/1.03  ------ Global Options
% 2.88/1.03  
% 2.88/1.03  --schedule                              default
% 2.88/1.03  --add_important_lit                     false
% 2.88/1.03  --prop_solver_per_cl                    1000
% 2.88/1.03  --min_unsat_core                        false
% 2.88/1.03  --soft_assumptions                      false
% 2.88/1.03  --soft_lemma_size                       3
% 2.88/1.03  --prop_impl_unit_size                   0
% 2.88/1.03  --prop_impl_unit                        []
% 2.88/1.03  --share_sel_clauses                     true
% 2.88/1.03  --reset_solvers                         false
% 2.88/1.03  --bc_imp_inh                            [conj_cone]
% 2.88/1.03  --conj_cone_tolerance                   3.
% 2.88/1.03  --extra_neg_conj                        none
% 2.88/1.03  --large_theory_mode                     true
% 2.88/1.03  --prolific_symb_bound                   200
% 2.88/1.03  --lt_threshold                          2000
% 2.88/1.03  --clause_weak_htbl                      true
% 2.88/1.03  --gc_record_bc_elim                     false
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing Options
% 2.88/1.03  
% 2.88/1.03  --preprocessing_flag                    true
% 2.88/1.03  --time_out_prep_mult                    0.1
% 2.88/1.03  --splitting_mode                        input
% 2.88/1.03  --splitting_grd                         true
% 2.88/1.03  --splitting_cvd                         false
% 2.88/1.03  --splitting_cvd_svl                     false
% 2.88/1.03  --splitting_nvd                         32
% 2.88/1.03  --sub_typing                            true
% 2.88/1.03  --prep_gs_sim                           true
% 2.88/1.03  --prep_unflatten                        true
% 2.88/1.03  --prep_res_sim                          true
% 2.88/1.03  --prep_upred                            true
% 2.88/1.03  --prep_sem_filter                       exhaustive
% 2.88/1.03  --prep_sem_filter_out                   false
% 2.88/1.03  --pred_elim                             true
% 2.88/1.03  --res_sim_input                         true
% 2.88/1.03  --eq_ax_congr_red                       true
% 2.88/1.03  --pure_diseq_elim                       true
% 2.88/1.03  --brand_transform                       false
% 2.88/1.03  --non_eq_to_eq                          false
% 2.88/1.03  --prep_def_merge                        true
% 2.88/1.03  --prep_def_merge_prop_impl              false
% 2.88/1.03  --prep_def_merge_mbd                    true
% 2.88/1.03  --prep_def_merge_tr_red                 false
% 2.88/1.03  --prep_def_merge_tr_cl                  false
% 2.88/1.03  --smt_preprocessing                     true
% 2.88/1.03  --smt_ac_axioms                         fast
% 2.88/1.03  --preprocessed_out                      false
% 2.88/1.03  --preprocessed_stats                    false
% 2.88/1.03  
% 2.88/1.03  ------ Abstraction refinement Options
% 2.88/1.03  
% 2.88/1.03  --abstr_ref                             []
% 2.88/1.03  --abstr_ref_prep                        false
% 2.88/1.03  --abstr_ref_until_sat                   false
% 2.88/1.03  --abstr_ref_sig_restrict                funpre
% 2.88/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.03  --abstr_ref_under                       []
% 2.88/1.03  
% 2.88/1.03  ------ SAT Options
% 2.88/1.03  
% 2.88/1.03  --sat_mode                              false
% 2.88/1.03  --sat_fm_restart_options                ""
% 2.88/1.03  --sat_gr_def                            false
% 2.88/1.03  --sat_epr_types                         true
% 2.88/1.03  --sat_non_cyclic_types                  false
% 2.88/1.03  --sat_finite_models                     false
% 2.88/1.03  --sat_fm_lemmas                         false
% 2.88/1.03  --sat_fm_prep                           false
% 2.88/1.03  --sat_fm_uc_incr                        true
% 2.88/1.03  --sat_out_model                         small
% 2.88/1.03  --sat_out_clauses                       false
% 2.88/1.03  
% 2.88/1.03  ------ QBF Options
% 2.88/1.03  
% 2.88/1.03  --qbf_mode                              false
% 2.88/1.03  --qbf_elim_univ                         false
% 2.88/1.03  --qbf_dom_inst                          none
% 2.88/1.03  --qbf_dom_pre_inst                      false
% 2.88/1.03  --qbf_sk_in                             false
% 2.88/1.03  --qbf_pred_elim                         true
% 2.88/1.03  --qbf_split                             512
% 2.88/1.03  
% 2.88/1.03  ------ BMC1 Options
% 2.88/1.03  
% 2.88/1.03  --bmc1_incremental                      false
% 2.88/1.03  --bmc1_axioms                           reachable_all
% 2.88/1.03  --bmc1_min_bound                        0
% 2.88/1.03  --bmc1_max_bound                        -1
% 2.88/1.03  --bmc1_max_bound_default                -1
% 2.88/1.03  --bmc1_symbol_reachability              true
% 2.88/1.03  --bmc1_property_lemmas                  false
% 2.88/1.03  --bmc1_k_induction                      false
% 2.88/1.03  --bmc1_non_equiv_states                 false
% 2.88/1.03  --bmc1_deadlock                         false
% 2.88/1.03  --bmc1_ucm                              false
% 2.88/1.03  --bmc1_add_unsat_core                   none
% 2.88/1.03  --bmc1_unsat_core_children              false
% 2.88/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.03  --bmc1_out_stat                         full
% 2.88/1.03  --bmc1_ground_init                      false
% 2.88/1.03  --bmc1_pre_inst_next_state              false
% 2.88/1.03  --bmc1_pre_inst_state                   false
% 2.88/1.03  --bmc1_pre_inst_reach_state             false
% 2.88/1.03  --bmc1_out_unsat_core                   false
% 2.88/1.03  --bmc1_aig_witness_out                  false
% 2.88/1.03  --bmc1_verbose                          false
% 2.88/1.03  --bmc1_dump_clauses_tptp                false
% 2.88/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.03  --bmc1_dump_file                        -
% 2.88/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.03  --bmc1_ucm_extend_mode                  1
% 2.88/1.03  --bmc1_ucm_init_mode                    2
% 2.88/1.03  --bmc1_ucm_cone_mode                    none
% 2.88/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.03  --bmc1_ucm_relax_model                  4
% 2.88/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.03  --bmc1_ucm_layered_model                none
% 2.88/1.03  --bmc1_ucm_max_lemma_size               10
% 2.88/1.03  
% 2.88/1.03  ------ AIG Options
% 2.88/1.03  
% 2.88/1.03  --aig_mode                              false
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation Options
% 2.88/1.03  
% 2.88/1.03  --instantiation_flag                    true
% 2.88/1.03  --inst_sos_flag                         false
% 2.88/1.03  --inst_sos_phase                        true
% 2.88/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel_side                     none
% 2.88/1.03  --inst_solver_per_active                1400
% 2.88/1.03  --inst_solver_calls_frac                1.
% 2.88/1.03  --inst_passive_queue_type               priority_queues
% 2.88/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.03  --inst_passive_queues_freq              [25;2]
% 2.88/1.03  --inst_dismatching                      true
% 2.88/1.03  --inst_eager_unprocessed_to_passive     true
% 2.88/1.03  --inst_prop_sim_given                   true
% 2.88/1.03  --inst_prop_sim_new                     false
% 2.88/1.03  --inst_subs_new                         false
% 2.88/1.03  --inst_eq_res_simp                      false
% 2.88/1.03  --inst_subs_given                       false
% 2.88/1.03  --inst_orphan_elimination               true
% 2.88/1.03  --inst_learning_loop_flag               true
% 2.88/1.03  --inst_learning_start                   3000
% 2.88/1.03  --inst_learning_factor                  2
% 2.88/1.03  --inst_start_prop_sim_after_learn       3
% 2.88/1.03  --inst_sel_renew                        solver
% 2.88/1.03  --inst_lit_activity_flag                true
% 2.88/1.03  --inst_restr_to_given                   false
% 2.88/1.03  --inst_activity_threshold               500
% 2.88/1.03  --inst_out_proof                        true
% 2.88/1.03  
% 2.88/1.03  ------ Resolution Options
% 2.88/1.03  
% 2.88/1.03  --resolution_flag                       false
% 2.88/1.03  --res_lit_sel                           adaptive
% 2.88/1.03  --res_lit_sel_side                      none
% 2.88/1.03  --res_ordering                          kbo
% 2.88/1.03  --res_to_prop_solver                    active
% 2.88/1.03  --res_prop_simpl_new                    false
% 2.88/1.03  --res_prop_simpl_given                  true
% 2.88/1.03  --res_passive_queue_type                priority_queues
% 2.88/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.03  --res_passive_queues_freq               [15;5]
% 2.88/1.03  --res_forward_subs                      full
% 2.88/1.03  --res_backward_subs                     full
% 2.88/1.03  --res_forward_subs_resolution           true
% 2.88/1.03  --res_backward_subs_resolution          true
% 2.88/1.03  --res_orphan_elimination                true
% 2.88/1.03  --res_time_limit                        2.
% 2.88/1.03  --res_out_proof                         true
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Options
% 2.88/1.03  
% 2.88/1.03  --superposition_flag                    true
% 2.88/1.03  --sup_passive_queue_type                priority_queues
% 2.88/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.03  --demod_completeness_check              fast
% 2.88/1.03  --demod_use_ground                      true
% 2.88/1.03  --sup_to_prop_solver                    passive
% 2.88/1.03  --sup_prop_simpl_new                    true
% 2.88/1.03  --sup_prop_simpl_given                  true
% 2.88/1.03  --sup_fun_splitting                     false
% 2.88/1.03  --sup_smt_interval                      50000
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Simplification Setup
% 2.88/1.03  
% 2.88/1.03  --sup_indices_passive                   []
% 2.88/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_full_bw                           [BwDemod]
% 2.88/1.03  --sup_immed_triv                        [TrivRules]
% 2.88/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_immed_bw_main                     []
% 2.88/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  
% 2.88/1.03  ------ Combination Options
% 2.88/1.03  
% 2.88/1.03  --comb_res_mult                         3
% 2.88/1.03  --comb_sup_mult                         2
% 2.88/1.03  --comb_inst_mult                        10
% 2.88/1.03  
% 2.88/1.03  ------ Debug Options
% 2.88/1.03  
% 2.88/1.03  --dbg_backtrace                         false
% 2.88/1.03  --dbg_dump_prop_clauses                 false
% 2.88/1.03  --dbg_dump_prop_clauses_file            -
% 2.88/1.03  --dbg_out_stat                          false
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  ------ Proving...
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  % SZS status Theorem for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  fof(f6,axiom,(
% 2.88/1.03    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f29,plain,(
% 2.88/1.03    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.88/1.03    introduced(choice_axiom,[])).
% 2.88/1.03  
% 2.88/1.03  fof(f30,plain,(
% 2.88/1.03    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f29])).
% 2.88/1.03  
% 2.88/1.03  fof(f46,plain,(
% 2.88/1.03    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f30])).
% 2.88/1.03  
% 2.88/1.03  fof(f7,axiom,(
% 2.88/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f15,plain,(
% 2.88/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.88/1.03    inference(ennf_transformation,[],[f7])).
% 2.88/1.03  
% 2.88/1.03  fof(f16,plain,(
% 2.88/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.88/1.03    inference(flattening,[],[f15])).
% 2.88/1.03  
% 2.88/1.03  fof(f47,plain,(
% 2.88/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f16])).
% 2.88/1.03  
% 2.88/1.03  fof(f10,axiom,(
% 2.88/1.03    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f20,plain,(
% 2.88/1.03    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f10])).
% 2.88/1.03  
% 2.88/1.03  fof(f21,plain,(
% 2.88/1.03    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(flattening,[],[f20])).
% 2.88/1.03  
% 2.88/1.03  fof(f53,plain,(
% 2.88/1.03    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f21])).
% 2.88/1.03  
% 2.88/1.03  fof(f12,conjecture,(
% 2.88/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f13,negated_conjecture,(
% 2.88/1.03    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 2.88/1.03    inference(negated_conjecture,[],[f12])).
% 2.88/1.03  
% 2.88/1.03  fof(f24,plain,(
% 2.88/1.03    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f13])).
% 2.88/1.03  
% 2.88/1.03  fof(f25,plain,(
% 2.88/1.03    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.88/1.03    inference(flattening,[],[f24])).
% 2.88/1.03  
% 2.88/1.03  fof(f36,plain,(
% 2.88/1.03    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 2.88/1.03    introduced(choice_axiom,[])).
% 2.88/1.03  
% 2.88/1.03  fof(f35,plain,(
% 2.88/1.03    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 2.88/1.03    introduced(choice_axiom,[])).
% 2.88/1.03  
% 2.88/1.03  fof(f37,plain,(
% 2.88/1.03    (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 2.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36,f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f60,plain,(
% 2.88/1.03    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f59,plain,(
% 2.88/1.03    l1_orders_2(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f55,plain,(
% 2.88/1.03    ~v2_struct_0(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f56,plain,(
% 2.88/1.03    v3_orders_2(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f57,plain,(
% 2.88/1.03    v4_orders_2(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f58,plain,(
% 2.88/1.03    v5_orders_2(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f3,axiom,(
% 2.88/1.03    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f28,plain,(
% 2.88/1.03    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.88/1.03    inference(nnf_transformation,[],[f3])).
% 2.88/1.03  
% 2.88/1.03  fof(f43,plain,(
% 2.88/1.03    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f28])).
% 2.88/1.03  
% 2.88/1.03  fof(f61,plain,(
% 2.88/1.03    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))),
% 2.88/1.03    inference(cnf_transformation,[],[f37])).
% 2.88/1.03  
% 2.88/1.03  fof(f5,axiom,(
% 2.88/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f14,plain,(
% 2.88/1.03    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 2.88/1.03    inference(ennf_transformation,[],[f5])).
% 2.88/1.03  
% 2.88/1.03  fof(f45,plain,(
% 2.88/1.03    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f14])).
% 2.88/1.03  
% 2.88/1.03  fof(f4,axiom,(
% 2.88/1.03    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f44,plain,(
% 2.88/1.03    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.88/1.03    inference(cnf_transformation,[],[f4])).
% 2.88/1.03  
% 2.88/1.03  fof(f2,axiom,(
% 2.88/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f41,plain,(
% 2.88/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f2])).
% 2.88/1.03  
% 2.88/1.03  fof(f1,axiom,(
% 2.88/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f26,plain,(
% 2.88/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.03    inference(nnf_transformation,[],[f1])).
% 2.88/1.03  
% 2.88/1.03  fof(f27,plain,(
% 2.88/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.03    inference(flattening,[],[f26])).
% 2.88/1.03  
% 2.88/1.03  fof(f40,plain,(
% 2.88/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f27])).
% 2.88/1.03  
% 2.88/1.03  fof(f11,axiom,(
% 2.88/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f22,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f11])).
% 2.88/1.03  
% 2.88/1.03  fof(f23,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(flattening,[],[f22])).
% 2.88/1.03  
% 2.88/1.03  fof(f54,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f23])).
% 2.88/1.03  
% 2.88/1.03  fof(f8,axiom,(
% 2.88/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f17,plain,(
% 2.88/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.88/1.03    inference(ennf_transformation,[],[f8])).
% 2.88/1.03  
% 2.88/1.03  fof(f48,plain,(
% 2.88/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f17])).
% 2.88/1.03  
% 2.88/1.03  fof(f9,axiom,(
% 2.88/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 2.88/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f18,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f9])).
% 2.88/1.03  
% 2.88/1.03  fof(f19,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(flattening,[],[f18])).
% 2.88/1.03  
% 2.88/1.03  fof(f31,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(nnf_transformation,[],[f19])).
% 2.88/1.03  
% 2.88/1.03  fof(f32,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(rectify,[],[f31])).
% 2.88/1.03  
% 2.88/1.03  fof(f33,plain,(
% 2.88/1.03    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.88/1.03    introduced(choice_axiom,[])).
% 2.88/1.03  
% 2.88/1.03  fof(f34,plain,(
% 2.88/1.03    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.88/1.03  
% 2.88/1.03  fof(f49,plain,(
% 2.88/1.03    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f34])).
% 2.88/1.03  
% 2.88/1.03  fof(f65,plain,(
% 2.88/1.03    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.88/1.03    inference(equality_resolution,[],[f49])).
% 2.88/1.03  
% 2.88/1.03  fof(f38,plain,(
% 2.88/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.88/1.03    inference(cnf_transformation,[],[f27])).
% 2.88/1.03  
% 2.88/1.03  fof(f63,plain,(
% 2.88/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.88/1.03    inference(equality_resolution,[],[f38])).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1461,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/1.03      | m2_orders_2(X3,X4,X5)
% 2.88/1.03      | X3 != X0
% 2.88/1.03      | X4 != X1
% 2.88/1.03      | X5 != X2 ),
% 2.88/1.03      theory(equality) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1959,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,X2)
% 2.88/1.03      | ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
% 2.88/1.03      | X0 != sK0(k4_orders_2(sK2,sK3))
% 2.88/1.03      | X2 != sK3
% 2.88/1.03      | X1 != sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1461]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2592,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,sK3)
% 2.88/1.03      | ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
% 2.88/1.03      | X0 != sK0(k4_orders_2(sK2,sK3))
% 2.88/1.03      | X1 != sK2
% 2.88/1.03      | sK3 != sK3 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1959]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4398,plain,
% 2.88/1.03      ( ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
% 2.88/1.03      | m2_orders_2(k1_xboole_0,X0,sK3)
% 2.88/1.03      | X0 != sK2
% 2.88/1.03      | sK3 != sK3
% 2.88/1.03      | k1_xboole_0 != sK0(k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_2592]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4422,plain,
% 2.88/1.03      ( ~ m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3)
% 2.88/1.03      | m2_orders_2(k1_xboole_0,sK2,sK3)
% 2.88/1.03      | sK3 != sK3
% 2.88/1.03      | sK2 != sK2
% 2.88/1.03      | k1_xboole_0 != sK0(k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_4398]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_8,plain,
% 2.88/1.03      ( m1_subset_1(sK0(X0),X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_9,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.88/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_301,plain,
% 2.88/1.03      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | X1 != X2 | sK0(X2) != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_302,plain,
% 2.88/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_301]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_15,plain,
% 2.88/1.03      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1)
% 2.88/1.03      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_18,negated_conjecture,
% 2.88/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
% 2.88/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_506,plain,
% 2.88/1.03      ( v2_struct_0(X0)
% 2.88/1.03      | ~ v3_orders_2(X0)
% 2.88/1.03      | ~ v4_orders_2(X0)
% 2.88/1.03      | ~ v5_orders_2(X0)
% 2.88/1.03      | ~ l1_orders_2(X0)
% 2.88/1.03      | ~ v1_xboole_0(k4_orders_2(X0,X1))
% 2.88/1.03      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK3 != X1 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_507,plain,
% 2.88/1.03      ( v2_struct_0(X0)
% 2.88/1.03      | ~ v3_orders_2(X0)
% 2.88/1.03      | ~ v4_orders_2(X0)
% 2.88/1.03      | ~ v5_orders_2(X0)
% 2.88/1.03      | ~ l1_orders_2(X0)
% 2.88/1.03      | ~ v1_xboole_0(k4_orders_2(X0,sK3))
% 2.88/1.03      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_506]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_19,negated_conjecture,
% 2.88/1.03      ( l1_orders_2(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_622,plain,
% 2.88/1.03      ( v2_struct_0(X0)
% 2.88/1.03      | ~ v3_orders_2(X0)
% 2.88/1.03      | ~ v4_orders_2(X0)
% 2.88/1.03      | ~ v5_orders_2(X0)
% 2.88/1.03      | ~ v1_xboole_0(k4_orders_2(X0,sK3))
% 2.88/1.03      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK2 != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_507,c_19]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_623,plain,
% 2.88/1.03      ( v2_struct_0(sK2)
% 2.88/1.03      | ~ v3_orders_2(sK2)
% 2.88/1.03      | ~ v4_orders_2(sK2)
% 2.88/1.03      | ~ v5_orders_2(sK2)
% 2.88/1.03      | ~ v1_xboole_0(k4_orders_2(sK2,sK3))
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_622]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_23,negated_conjecture,
% 2.88/1.03      ( ~ v2_struct_0(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_22,negated_conjecture,
% 2.88/1.03      ( v3_orders_2(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_21,negated_conjecture,
% 2.88/1.03      ( v4_orders_2(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_20,negated_conjecture,
% 2.88/1.03      ( v5_orders_2(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_625,plain,
% 2.88/1.03      ( ~ v1_xboole_0(k4_orders_2(sK2,sK3))
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_623,c_23,c_22,c_21,c_20]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_772,plain,
% 2.88/1.03      ( r2_hidden(sK0(X0),X0)
% 2.88/1.03      | k4_orders_2(sK2,sK3) != X0
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_302,c_625]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_773,plain,
% 2.88/1.03      ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_772]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1826,plain,
% 2.88/1.03      ( r2_hidden(sK0(k4_orders_2(sK2,sK3)),k4_orders_2(sK2,sK3)) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4,plain,
% 2.88/1.03      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 2.88/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1830,plain,
% 2.88/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.88/1.03      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_17,negated_conjecture,
% 2.88/1.03      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_7,plain,
% 2.88/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1828,plain,
% 2.88/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.88/1.03      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2759,plain,
% 2.88/1.03      ( r1_tarski(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 2.88/1.03      | r1_tarski(k3_tarski(X0),k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_17,c_1828]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3023,plain,
% 2.88/1.03      ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 2.88/1.03      | r1_tarski(k3_tarski(k1_tarski(X0)),k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1830,c_2759]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_6,plain,
% 2.88/1.03      ( k3_tarski(k1_tarski(X0)) = X0 ),
% 2.88/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3026,plain,
% 2.88/1.03      ( r2_hidden(X0,k4_orders_2(sK2,sK3)) != iProver_top
% 2.88/1.03      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_3023,c_6]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3203,plain,
% 2.88/1.03      ( r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1826,c_3026]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3,plain,
% 2.88/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2702,plain,
% 2.88/1.03      ( r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2705,plain,
% 2.88/1.03      ( r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_2702]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_0,plain,
% 2.88/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.88/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2077,plain,
% 2.88/1.03      ( ~ r1_tarski(X0,sK0(k4_orders_2(sK2,sK3)))
% 2.88/1.03      | ~ r1_tarski(sK0(k4_orders_2(sK2,sK3)),X0)
% 2.88/1.03      | X0 = sK0(k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2701,plain,
% 2.88/1.03      ( ~ r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0)
% 2.88/1.03      | ~ r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3)))
% 2.88/1.03      | k1_xboole_0 = sK0(k4_orders_2(sK2,sK3)) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_2077]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2703,plain,
% 2.88/1.03      ( k1_xboole_0 = sK0(k4_orders_2(sK2,sK3))
% 2.88/1.03      | r1_tarski(sK0(k4_orders_2(sK2,sK3)),k1_xboole_0) != iProver_top
% 2.88/1.03      | r1_tarski(k1_xboole_0,sK0(k4_orders_2(sK2,sK3))) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_2701]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1831,plain,
% 2.88/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_16,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/1.03      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1) ),
% 2.88/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_416,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.88/1.03      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK3 != X2 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_417,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,X1,sK3)
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_416]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_726,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,X1,sK3)
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK2 != X1 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_417,c_19]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_727,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
% 2.88/1.03      | v2_struct_0(sK2)
% 2.88/1.03      | ~ v3_orders_2(sK2)
% 2.88/1.03      | ~ v4_orders_2(sK2)
% 2.88/1.03      | ~ v5_orders_2(sK2)
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_726]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_731,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_727,c_23,c_22,c_21,c_20]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1072,plain,
% 2.88/1.03      ( ~ m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) ),
% 2.88/1.03      inference(equality_resolution_simp,[status(thm)],[c_731]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1825,plain,
% 2.88/1.03      ( m2_orders_2(X0,sK2,sK3) != iProver_top
% 2.88/1.03      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_10,plain,
% 2.88/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1827,plain,
% 2.88/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.88/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2204,plain,
% 2.88/1.03      ( m2_orders_2(X0,sK2,sK3) != iProver_top
% 2.88/1.03      | r1_tarski(X0,k1_funct_1(sK3,u1_struct_0(sK2))) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1825,c_1827]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2441,plain,
% 2.88/1.03      ( m2_orders_2(k1_xboole_0,sK2,sK3) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1831,c_2204]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2452,plain,
% 2.88/1.03      ( ~ m2_orders_2(k1_xboole_0,sK2,sK3) ),
% 2.88/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2441]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1453,plain,( X0 = X0 ),theory(equality) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2167,plain,
% 2.88/1.03      ( sK3 = sK3 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1453]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_14,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,X2)
% 2.88/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1) ),
% 2.88/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_446,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,X2)
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK3 != X2 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_447,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,sK3)
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(X1,sK3))
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | ~ l1_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_446]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_705,plain,
% 2.88/1.03      ( m2_orders_2(X0,X1,sK3)
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(X1,sK3))
% 2.88/1.03      | v2_struct_0(X1)
% 2.88/1.03      | ~ v3_orders_2(X1)
% 2.88/1.03      | ~ v4_orders_2(X1)
% 2.88/1.03      | ~ v5_orders_2(X1)
% 2.88/1.03      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK2 != X1 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_447,c_19]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_706,plain,
% 2.88/1.03      ( m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
% 2.88/1.03      | v2_struct_0(sK2)
% 2.88/1.03      | ~ v3_orders_2(sK2)
% 2.88/1.03      | ~ v4_orders_2(sK2)
% 2.88/1.03      | ~ v5_orders_2(sK2)
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_705]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_710,plain,
% 2.88/1.03      ( m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_706,c_23,c_22,c_21,c_20]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_989,plain,
% 2.88/1.03      ( m2_orders_2(X0,sK2,sK3)
% 2.88/1.03      | k4_orders_2(sK2,sK3) != k4_orders_2(sK2,sK3)
% 2.88/1.03      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2))
% 2.88/1.03      | sK0(k4_orders_2(sK2,sK3)) != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_773,c_710]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_990,plain,
% 2.88/1.03      ( m2_orders_2(sK0(k4_orders_2(sK2,sK3)),sK2,sK3) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_989]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_75,plain,
% 2.88/1.03      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2,plain,
% 2.88/1.03      ( r1_tarski(X0,X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_71,plain,
% 2.88/1.03      ( r1_tarski(sK2,sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(contradiction,plain,
% 2.88/1.03      ( $false ),
% 2.88/1.03      inference(minisat,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_4422,c_3203,c_2705,c_2703,c_2452,c_2167,c_990,c_75,
% 2.88/1.03                 c_71]) ).
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  ------                               Statistics
% 2.88/1.03  
% 2.88/1.03  ------ General
% 2.88/1.03  
% 2.88/1.03  abstr_ref_over_cycles:                  0
% 2.88/1.03  abstr_ref_under_cycles:                 0
% 2.88/1.03  gc_basic_clause_elim:                   0
% 2.88/1.03  forced_gc_time:                         0
% 2.88/1.03  parsing_time:                           0.009
% 2.88/1.03  unif_index_cands_time:                  0.
% 2.88/1.03  unif_index_add_time:                    0.
% 2.88/1.03  orderings_time:                         0.
% 2.88/1.03  out_proof_time:                         0.012
% 2.88/1.03  total_time:                             0.171
% 2.88/1.03  num_of_symbols:                         53
% 2.88/1.03  num_of_terms:                           3292
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing
% 2.88/1.03  
% 2.88/1.03  num_of_splits:                          0
% 2.88/1.03  num_of_split_atoms:                     0
% 2.88/1.03  num_of_reused_defs:                     0
% 2.88/1.03  num_eq_ax_congr_red:                    13
% 2.88/1.03  num_of_sem_filtered_clauses:            1
% 2.88/1.03  num_of_subtypes:                        0
% 2.88/1.03  monotx_restored_types:                  0
% 2.88/1.03  sat_num_of_epr_types:                   0
% 2.88/1.03  sat_num_of_non_cyclic_types:            0
% 2.88/1.03  sat_guarded_non_collapsed_types:        0
% 2.88/1.03  num_pure_diseq_elim:                    0
% 2.88/1.03  simp_replaced_by:                       0
% 2.88/1.03  res_preprocessed:                       91
% 2.88/1.03  prep_upred:                             0
% 2.88/1.03  prep_unflattend:                        81
% 2.88/1.03  smt_new_axioms:                         0
% 2.88/1.03  pred_elim_cands:                        3
% 2.88/1.03  pred_elim:                              8
% 2.88/1.03  pred_elim_cl:                           8
% 2.88/1.03  pred_elim_cycles:                       14
% 2.88/1.03  merged_defs:                            14
% 2.88/1.03  merged_defs_ncl:                        0
% 2.88/1.03  bin_hyper_res:                          14
% 2.88/1.03  prep_cycles:                            4
% 2.88/1.03  pred_elim_time:                         0.021
% 2.88/1.03  splitting_time:                         0.
% 2.88/1.03  sem_filter_time:                        0.
% 2.88/1.03  monotx_time:                            0.
% 2.88/1.03  subtype_inf_time:                       0.
% 2.88/1.03  
% 2.88/1.03  ------ Problem properties
% 2.88/1.03  
% 2.88/1.03  clauses:                                15
% 2.88/1.03  conjectures:                            1
% 2.88/1.03  epr:                                    4
% 2.88/1.03  horn:                                   14
% 2.88/1.03  ground:                                 2
% 2.88/1.03  unary:                                  5
% 2.88/1.03  binary:                                 7
% 2.88/1.03  lits:                                   28
% 2.88/1.03  lits_eq:                                5
% 2.88/1.03  fd_pure:                                0
% 2.88/1.03  fd_pseudo:                              0
% 2.88/1.03  fd_cond:                                2
% 2.88/1.03  fd_pseudo_cond:                         1
% 2.88/1.03  ac_symbols:                             0
% 2.88/1.03  
% 2.88/1.03  ------ Propositional Solver
% 2.88/1.03  
% 2.88/1.03  prop_solver_calls:                      27
% 2.88/1.03  prop_fast_solver_calls:                 746
% 2.88/1.03  smt_solver_calls:                       0
% 2.88/1.03  smt_fast_solver_calls:                  0
% 2.88/1.03  prop_num_of_clauses:                    1487
% 2.88/1.03  prop_preprocess_simplified:             4146
% 2.88/1.03  prop_fo_subsumed:                       26
% 2.88/1.03  prop_solver_time:                       0.
% 2.88/1.03  smt_solver_time:                        0.
% 2.88/1.03  smt_fast_solver_time:                   0.
% 2.88/1.03  prop_fast_solver_time:                  0.
% 2.88/1.03  prop_unsat_core_time:                   0.
% 2.88/1.03  
% 2.88/1.03  ------ QBF
% 2.88/1.03  
% 2.88/1.03  qbf_q_res:                              0
% 2.88/1.03  qbf_num_tautologies:                    0
% 2.88/1.03  qbf_prep_cycles:                        0
% 2.88/1.03  
% 2.88/1.03  ------ BMC1
% 2.88/1.03  
% 2.88/1.03  bmc1_current_bound:                     -1
% 2.88/1.03  bmc1_last_solved_bound:                 -1
% 2.88/1.03  bmc1_unsat_core_size:                   -1
% 2.88/1.03  bmc1_unsat_core_parents_size:           -1
% 2.88/1.03  bmc1_merge_next_fun:                    0
% 2.88/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation
% 2.88/1.03  
% 2.88/1.03  inst_num_of_clauses:                    391
% 2.88/1.03  inst_num_in_passive:                    43
% 2.88/1.03  inst_num_in_active:                     198
% 2.88/1.03  inst_num_in_unprocessed:                149
% 2.88/1.03  inst_num_of_loops:                      227
% 2.88/1.03  inst_num_of_learning_restarts:          0
% 2.88/1.03  inst_num_moves_active_passive:          24
% 2.88/1.03  inst_lit_activity:                      0
% 2.88/1.03  inst_lit_activity_moves:                0
% 2.88/1.03  inst_num_tautologies:                   0
% 2.88/1.03  inst_num_prop_implied:                  0
% 2.88/1.03  inst_num_existing_simplified:           0
% 2.88/1.03  inst_num_eq_res_simplified:             0
% 2.88/1.03  inst_num_child_elim:                    0
% 2.88/1.03  inst_num_of_dismatching_blockings:      67
% 2.88/1.03  inst_num_of_non_proper_insts:           381
% 2.88/1.03  inst_num_of_duplicates:                 0
% 2.88/1.03  inst_inst_num_from_inst_to_res:         0
% 2.88/1.03  inst_dismatching_checking_time:         0.
% 2.88/1.03  
% 2.88/1.03  ------ Resolution
% 2.88/1.03  
% 2.88/1.03  res_num_of_clauses:                     0
% 2.88/1.03  res_num_in_passive:                     0
% 2.88/1.03  res_num_in_active:                      0
% 2.88/1.03  res_num_of_loops:                       95
% 2.88/1.03  res_forward_subset_subsumed:            49
% 2.88/1.03  res_backward_subset_subsumed:           0
% 2.88/1.03  res_forward_subsumed:                   0
% 2.88/1.03  res_backward_subsumed:                  0
% 2.88/1.03  res_forward_subsumption_resolution:     0
% 2.88/1.03  res_backward_subsumption_resolution:    0
% 2.88/1.03  res_clause_to_clause_subsumption:       284
% 2.88/1.03  res_orphan_elimination:                 0
% 2.88/1.03  res_tautology_del:                      73
% 2.88/1.03  res_num_eq_res_simplified:              5
% 2.88/1.03  res_num_sel_changes:                    0
% 2.88/1.03  res_moves_from_active_to_pass:          0
% 2.88/1.03  
% 2.88/1.03  ------ Superposition
% 2.88/1.03  
% 2.88/1.03  sup_time_total:                         0.
% 2.88/1.03  sup_time_generating:                    0.
% 2.88/1.03  sup_time_sim_full:                      0.
% 2.88/1.03  sup_time_sim_immed:                     0.
% 2.88/1.03  
% 2.88/1.03  sup_num_of_clauses:                     67
% 2.88/1.03  sup_num_in_active:                      42
% 2.88/1.03  sup_num_in_passive:                     25
% 2.88/1.03  sup_num_of_loops:                       44
% 2.88/1.03  sup_fw_superposition:                   47
% 2.88/1.03  sup_bw_superposition:                   31
% 2.88/1.03  sup_immediate_simplified:               11
% 2.88/1.03  sup_given_eliminated:                   0
% 2.88/1.03  comparisons_done:                       0
% 2.88/1.03  comparisons_avoided:                    0
% 2.88/1.03  
% 2.88/1.03  ------ Simplifications
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  sim_fw_subset_subsumed:                 1
% 2.88/1.03  sim_bw_subset_subsumed:                 1
% 2.88/1.03  sim_fw_subsumed:                        6
% 2.88/1.03  sim_bw_subsumed:                        0
% 2.88/1.03  sim_fw_subsumption_res:                 1
% 2.88/1.03  sim_bw_subsumption_res:                 0
% 2.88/1.03  sim_tautology_del:                      3
% 2.88/1.03  sim_eq_tautology_del:                   5
% 2.88/1.03  sim_eq_res_simp:                        0
% 2.88/1.03  sim_fw_demodulated:                     0
% 2.88/1.03  sim_bw_demodulated:                     2
% 2.88/1.03  sim_light_normalised:                   5
% 2.88/1.03  sim_joinable_taut:                      0
% 2.88/1.03  sim_joinable_simp:                      0
% 2.88/1.03  sim_ac_normalised:                      0
% 2.88/1.03  sim_smt_subsumption:                    0
% 2.88/1.03  
%------------------------------------------------------------------------------
