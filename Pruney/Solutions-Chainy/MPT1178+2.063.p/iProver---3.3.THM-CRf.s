%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:09 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 715 expanded)
%              Number of clauses        :   84 ( 173 expanded)
%              Number of leaves         :   16 ( 198 expanded)
%              Depth                    :   20
%              Number of atoms          :  651 (4417 expanded)
%              Number of equality atoms :  172 ( 777 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f17])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4))
        & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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

fof(f36,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))
    & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f35,f34])).

fof(f56,plain,(
    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f57,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f23,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f32])).

fof(f48,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_6,plain,
    ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_267,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_268,plain,
    ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_540,plain,
    ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_16])).

cnf(c_541,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_545,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_20,c_19,c_18,c_17])).

cnf(c_1098,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_545])).

cnf(c_1921,plain,
    ( k4_orders_2(sK3,sK4) = X0
    | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_7,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_393,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_394,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_564,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_394,c_16])).

cnf(c_565,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_20,c_19,c_18,c_17])).

cnf(c_1094,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_569])).

cnf(c_1132,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
    inference(prop_impl,[status(thm)],[c_1094])).

cnf(c_1922,plain,
    ( m2_orders_2(X0,sK3,sK4) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1926,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2342,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1926])).

cnf(c_2399,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_2342])).

cnf(c_2421,plain,
    ( sK1(sK3,sK4,X0) = k1_xboole_0
    | k4_orders_2(sK3,sK4) = X0
    | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1921,c_2399])).

cnf(c_2423,plain,
    ( sK1(sK3,sK4,k1_xboole_0) = k1_xboole_0
    | k4_orders_2(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2027,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_2057,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2303,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | sK1(sK3,sK4,X0) != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_2305,plain,
    ( m1_subset_1(sK1(sK3,sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | sK1(sK3,sK4,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_2098,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_2100,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_1591,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1600,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_9,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_230,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k4_orders_2(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_423,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_15])).

cnf(c_424,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_505,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_424,c_16])).

cnf(c_506,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( k4_orders_2(sK3,sK4) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_20,c_19,c_18,c_17])).

cnf(c_1106,plain,
    ( k4_orders_2(sK3,sK4) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_508])).

cnf(c_5,plain,
    ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_300,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_301,plain,
    ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_516,plain,
    ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4,X1),X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k4_orders_2(X0,sK4) = X1
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_16])).

cnf(c_517,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_20,c_19,c_18,c_17])).

cnf(c_1102,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_521])).

cnf(c_1103,plain,
    ( k4_orders_2(sK3,sK4) = X0
    | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) != iProver_top
    | r2_hidden(sK1(sK3,sK4,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_1105,plain,
    ( k4_orders_2(sK3,sK4) = k1_xboole_0
    | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) != iProver_top
    | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1104,plain,
    ( ~ m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
    | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0)
    | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_898,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | sK1(sK3,sK4,X0) != X2
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(resolution_lifted,[status(thm)],[c_219,c_545])).

cnf(c_899,plain,
    ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_900,plain,
    ( k4_orders_2(sK3,sK4) = X0
    | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_902,plain,
    ( k4_orders_2(sK3,sK4) = k1_xboole_0
    | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_901,plain,
    ( m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_219])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_744,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_333,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_334,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_606,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_16])).

cnf(c_607,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_20,c_19,c_18,c_17])).

cnf(c_667,plain,
    ( r2_hidden(sK1(sK3,sK4,X0),X0)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X1)
    | sK1(sK3,sK4,X0) != X1
    | k4_orders_2(sK3,sK4) = X0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_545,c_611])).

cnf(c_668,plain,
    ( r2_hidden(sK1(sK3,sK4,X0),X0)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,X0))
    | k4_orders_2(sK3,sK4) = X0 ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_670,plain,
    ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k1_xboole_0))
    | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_58,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2423,c_2305,c_2100,c_1600,c_1106,c_1105,c_1104,c_902,c_901,c_744,c_670,c_60,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:04:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.17/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.17/0.94  
% 1.17/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/0.94  
% 1.17/0.94  ------  iProver source info
% 1.17/0.94  
% 1.17/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.17/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/0.94  git: non_committed_changes: false
% 1.17/0.94  git: last_make_outside_of_git: false
% 1.17/0.94  
% 1.17/0.94  ------ 
% 1.17/0.94  
% 1.17/0.94  ------ Input Options
% 1.17/0.94  
% 1.17/0.94  --out_options                           all
% 1.17/0.94  --tptp_safe_out                         true
% 1.17/0.94  --problem_path                          ""
% 1.17/0.94  --include_path                          ""
% 1.17/0.94  --clausifier                            res/vclausify_rel
% 1.17/0.94  --clausifier_options                    --mode clausify
% 1.17/0.94  --stdin                                 false
% 1.17/0.94  --stats_out                             all
% 1.17/0.94  
% 1.17/0.94  ------ General Options
% 1.17/0.94  
% 1.17/0.94  --fof                                   false
% 1.17/0.94  --time_out_real                         305.
% 1.17/0.94  --time_out_virtual                      -1.
% 1.17/0.94  --symbol_type_check                     false
% 1.17/0.94  --clausify_out                          false
% 1.17/0.94  --sig_cnt_out                           false
% 1.17/0.94  --trig_cnt_out                          false
% 1.17/0.94  --trig_cnt_out_tolerance                1.
% 1.17/0.94  --trig_cnt_out_sk_spl                   false
% 1.17/0.94  --abstr_cl_out                          false
% 1.17/0.94  
% 1.17/0.94  ------ Global Options
% 1.17/0.94  
% 1.17/0.94  --schedule                              default
% 1.17/0.94  --add_important_lit                     false
% 1.17/0.94  --prop_solver_per_cl                    1000
% 1.17/0.94  --min_unsat_core                        false
% 1.17/0.94  --soft_assumptions                      false
% 1.17/0.94  --soft_lemma_size                       3
% 1.17/0.94  --prop_impl_unit_size                   0
% 1.17/0.94  --prop_impl_unit                        []
% 1.17/0.94  --share_sel_clauses                     true
% 1.17/0.94  --reset_solvers                         false
% 1.17/0.94  --bc_imp_inh                            [conj_cone]
% 1.17/0.94  --conj_cone_tolerance                   3.
% 1.17/0.94  --extra_neg_conj                        none
% 1.17/0.94  --large_theory_mode                     true
% 1.17/0.94  --prolific_symb_bound                   200
% 1.17/0.94  --lt_threshold                          2000
% 1.17/0.94  --clause_weak_htbl                      true
% 1.17/0.94  --gc_record_bc_elim                     false
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing Options
% 1.17/0.94  
% 1.17/0.94  --preprocessing_flag                    true
% 1.17/0.94  --time_out_prep_mult                    0.1
% 1.17/0.94  --splitting_mode                        input
% 1.17/0.94  --splitting_grd                         true
% 1.17/0.94  --splitting_cvd                         false
% 1.17/0.94  --splitting_cvd_svl                     false
% 1.17/0.94  --splitting_nvd                         32
% 1.17/0.94  --sub_typing                            true
% 1.17/0.94  --prep_gs_sim                           true
% 1.17/0.94  --prep_unflatten                        true
% 1.17/0.94  --prep_res_sim                          true
% 1.17/0.94  --prep_upred                            true
% 1.17/0.94  --prep_sem_filter                       exhaustive
% 1.17/0.94  --prep_sem_filter_out                   false
% 1.17/0.94  --pred_elim                             true
% 1.17/0.94  --res_sim_input                         true
% 1.17/0.94  --eq_ax_congr_red                       true
% 1.17/0.94  --pure_diseq_elim                       true
% 1.17/0.94  --brand_transform                       false
% 1.17/0.94  --non_eq_to_eq                          false
% 1.17/0.94  --prep_def_merge                        true
% 1.17/0.94  --prep_def_merge_prop_impl              false
% 1.17/0.94  --prep_def_merge_mbd                    true
% 1.17/0.94  --prep_def_merge_tr_red                 false
% 1.17/0.94  --prep_def_merge_tr_cl                  false
% 1.17/0.94  --smt_preprocessing                     true
% 1.17/0.94  --smt_ac_axioms                         fast
% 1.17/0.94  --preprocessed_out                      false
% 1.17/0.94  --preprocessed_stats                    false
% 1.17/0.94  
% 1.17/0.94  ------ Abstraction refinement Options
% 1.17/0.94  
% 1.17/0.94  --abstr_ref                             []
% 1.17/0.94  --abstr_ref_prep                        false
% 1.17/0.94  --abstr_ref_until_sat                   false
% 1.17/0.94  --abstr_ref_sig_restrict                funpre
% 1.17/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.94  --abstr_ref_under                       []
% 1.17/0.94  
% 1.17/0.94  ------ SAT Options
% 1.17/0.94  
% 1.17/0.94  --sat_mode                              false
% 1.17/0.94  --sat_fm_restart_options                ""
% 1.17/0.94  --sat_gr_def                            false
% 1.17/0.94  --sat_epr_types                         true
% 1.17/0.94  --sat_non_cyclic_types                  false
% 1.17/0.94  --sat_finite_models                     false
% 1.17/0.94  --sat_fm_lemmas                         false
% 1.17/0.94  --sat_fm_prep                           false
% 1.17/0.94  --sat_fm_uc_incr                        true
% 1.17/0.94  --sat_out_model                         small
% 1.17/0.94  --sat_out_clauses                       false
% 1.17/0.94  
% 1.17/0.94  ------ QBF Options
% 1.17/0.94  
% 1.17/0.94  --qbf_mode                              false
% 1.17/0.94  --qbf_elim_univ                         false
% 1.17/0.94  --qbf_dom_inst                          none
% 1.17/0.94  --qbf_dom_pre_inst                      false
% 1.17/0.94  --qbf_sk_in                             false
% 1.17/0.94  --qbf_pred_elim                         true
% 1.17/0.94  --qbf_split                             512
% 1.17/0.94  
% 1.17/0.94  ------ BMC1 Options
% 1.17/0.94  
% 1.17/0.94  --bmc1_incremental                      false
% 1.17/0.94  --bmc1_axioms                           reachable_all
% 1.17/0.94  --bmc1_min_bound                        0
% 1.17/0.94  --bmc1_max_bound                        -1
% 1.17/0.94  --bmc1_max_bound_default                -1
% 1.17/0.94  --bmc1_symbol_reachability              true
% 1.17/0.94  --bmc1_property_lemmas                  false
% 1.17/0.94  --bmc1_k_induction                      false
% 1.17/0.94  --bmc1_non_equiv_states                 false
% 1.17/0.94  --bmc1_deadlock                         false
% 1.17/0.94  --bmc1_ucm                              false
% 1.17/0.94  --bmc1_add_unsat_core                   none
% 1.17/0.94  --bmc1_unsat_core_children              false
% 1.17/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.94  --bmc1_out_stat                         full
% 1.17/0.94  --bmc1_ground_init                      false
% 1.17/0.94  --bmc1_pre_inst_next_state              false
% 1.17/0.94  --bmc1_pre_inst_state                   false
% 1.17/0.94  --bmc1_pre_inst_reach_state             false
% 1.17/0.94  --bmc1_out_unsat_core                   false
% 1.17/0.94  --bmc1_aig_witness_out                  false
% 1.17/0.94  --bmc1_verbose                          false
% 1.17/0.94  --bmc1_dump_clauses_tptp                false
% 1.17/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.94  --bmc1_dump_file                        -
% 1.17/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.94  --bmc1_ucm_extend_mode                  1
% 1.17/0.94  --bmc1_ucm_init_mode                    2
% 1.17/0.94  --bmc1_ucm_cone_mode                    none
% 1.17/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.94  --bmc1_ucm_relax_model                  4
% 1.17/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.94  --bmc1_ucm_layered_model                none
% 1.17/0.94  --bmc1_ucm_max_lemma_size               10
% 1.17/0.94  
% 1.17/0.94  ------ AIG Options
% 1.17/0.94  
% 1.17/0.94  --aig_mode                              false
% 1.17/0.94  
% 1.17/0.94  ------ Instantiation Options
% 1.17/0.94  
% 1.17/0.94  --instantiation_flag                    true
% 1.17/0.94  --inst_sos_flag                         false
% 1.17/0.94  --inst_sos_phase                        true
% 1.17/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.94  --inst_lit_sel_side                     num_symb
% 1.17/0.94  --inst_solver_per_active                1400
% 1.17/0.94  --inst_solver_calls_frac                1.
% 1.17/0.94  --inst_passive_queue_type               priority_queues
% 1.17/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/0.94  --inst_passive_queues_freq              [25;2]
% 1.17/0.94  --inst_dismatching                      true
% 1.17/0.94  --inst_eager_unprocessed_to_passive     true
% 1.17/0.94  --inst_prop_sim_given                   true
% 1.17/0.94  --inst_prop_sim_new                     false
% 1.17/0.94  --inst_subs_new                         false
% 1.17/0.94  --inst_eq_res_simp                      false
% 1.17/0.94  --inst_subs_given                       false
% 1.17/0.94  --inst_orphan_elimination               true
% 1.17/0.94  --inst_learning_loop_flag               true
% 1.17/0.94  --inst_learning_start                   3000
% 1.17/0.94  --inst_learning_factor                  2
% 1.17/0.94  --inst_start_prop_sim_after_learn       3
% 1.17/0.94  --inst_sel_renew                        solver
% 1.17/0.94  --inst_lit_activity_flag                true
% 1.17/0.94  --inst_restr_to_given                   false
% 1.17/0.94  --inst_activity_threshold               500
% 1.17/0.94  --inst_out_proof                        true
% 1.17/0.94  
% 1.17/0.94  ------ Resolution Options
% 1.17/0.94  
% 1.17/0.94  --resolution_flag                       true
% 1.17/0.94  --res_lit_sel                           adaptive
% 1.17/0.94  --res_lit_sel_side                      none
% 1.17/0.94  --res_ordering                          kbo
% 1.17/0.94  --res_to_prop_solver                    active
% 1.17/0.94  --res_prop_simpl_new                    false
% 1.17/0.94  --res_prop_simpl_given                  true
% 1.17/0.94  --res_passive_queue_type                priority_queues
% 1.17/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/0.94  --res_passive_queues_freq               [15;5]
% 1.17/0.94  --res_forward_subs                      full
% 1.17/0.94  --res_backward_subs                     full
% 1.17/0.94  --res_forward_subs_resolution           true
% 1.17/0.94  --res_backward_subs_resolution          true
% 1.17/0.94  --res_orphan_elimination                true
% 1.17/0.94  --res_time_limit                        2.
% 1.17/0.94  --res_out_proof                         true
% 1.17/0.94  
% 1.17/0.94  ------ Superposition Options
% 1.17/0.94  
% 1.17/0.94  --superposition_flag                    true
% 1.17/0.94  --sup_passive_queue_type                priority_queues
% 1.17/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.94  --demod_completeness_check              fast
% 1.17/0.94  --demod_use_ground                      true
% 1.17/0.94  --sup_to_prop_solver                    passive
% 1.17/0.94  --sup_prop_simpl_new                    true
% 1.17/0.94  --sup_prop_simpl_given                  true
% 1.17/0.94  --sup_fun_splitting                     false
% 1.17/0.94  --sup_smt_interval                      50000
% 1.17/0.94  
% 1.17/0.94  ------ Superposition Simplification Setup
% 1.17/0.94  
% 1.17/0.94  --sup_indices_passive                   []
% 1.17/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_full_bw                           [BwDemod]
% 1.17/0.94  --sup_immed_triv                        [TrivRules]
% 1.17/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_immed_bw_main                     []
% 1.17/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.94  
% 1.17/0.94  ------ Combination Options
% 1.17/0.94  
% 1.17/0.94  --comb_res_mult                         3
% 1.17/0.94  --comb_sup_mult                         2
% 1.17/0.94  --comb_inst_mult                        10
% 1.17/0.94  
% 1.17/0.94  ------ Debug Options
% 1.17/0.94  
% 1.17/0.94  --dbg_backtrace                         false
% 1.17/0.94  --dbg_dump_prop_clauses                 false
% 1.17/0.94  --dbg_dump_prop_clauses_file            -
% 1.17/0.94  --dbg_out_stat                          false
% 1.17/0.94  ------ Parsing...
% 1.17/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.17/0.94  ------ Proving...
% 1.17/0.94  ------ Problem Properties 
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  clauses                                 14
% 1.17/0.94  conjectures                             1
% 1.17/0.94  EPR                                     0
% 1.17/0.94  Horn                                    11
% 1.17/0.94  unary                                   3
% 1.17/0.94  binary                                  7
% 1.17/0.94  lits                                    29
% 1.17/0.94  lits eq                                 10
% 1.17/0.94  fd_pure                                 0
% 1.17/0.94  fd_pseudo                               0
% 1.17/0.94  fd_cond                                 4
% 1.17/0.94  fd_pseudo_cond                          0
% 1.17/0.94  AC symbols                              0
% 1.17/0.94  
% 1.17/0.94  ------ Schedule dynamic 5 is on 
% 1.17/0.94  
% 1.17/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  ------ 
% 1.17/0.94  Current options:
% 1.17/0.94  ------ 
% 1.17/0.94  
% 1.17/0.94  ------ Input Options
% 1.17/0.94  
% 1.17/0.94  --out_options                           all
% 1.17/0.94  --tptp_safe_out                         true
% 1.17/0.94  --problem_path                          ""
% 1.17/0.94  --include_path                          ""
% 1.17/0.94  --clausifier                            res/vclausify_rel
% 1.17/0.94  --clausifier_options                    --mode clausify
% 1.17/0.94  --stdin                                 false
% 1.17/0.94  --stats_out                             all
% 1.17/0.94  
% 1.17/0.94  ------ General Options
% 1.17/0.94  
% 1.17/0.94  --fof                                   false
% 1.17/0.94  --time_out_real                         305.
% 1.17/0.94  --time_out_virtual                      -1.
% 1.17/0.94  --symbol_type_check                     false
% 1.17/0.94  --clausify_out                          false
% 1.17/0.94  --sig_cnt_out                           false
% 1.17/0.94  --trig_cnt_out                          false
% 1.17/0.94  --trig_cnt_out_tolerance                1.
% 1.17/0.94  --trig_cnt_out_sk_spl                   false
% 1.17/0.94  --abstr_cl_out                          false
% 1.17/0.94  
% 1.17/0.94  ------ Global Options
% 1.17/0.94  
% 1.17/0.94  --schedule                              default
% 1.17/0.94  --add_important_lit                     false
% 1.17/0.94  --prop_solver_per_cl                    1000
% 1.17/0.94  --min_unsat_core                        false
% 1.17/0.94  --soft_assumptions                      false
% 1.17/0.94  --soft_lemma_size                       3
% 1.17/0.94  --prop_impl_unit_size                   0
% 1.17/0.94  --prop_impl_unit                        []
% 1.17/0.94  --share_sel_clauses                     true
% 1.17/0.94  --reset_solvers                         false
% 1.17/0.94  --bc_imp_inh                            [conj_cone]
% 1.17/0.94  --conj_cone_tolerance                   3.
% 1.17/0.94  --extra_neg_conj                        none
% 1.17/0.94  --large_theory_mode                     true
% 1.17/0.94  --prolific_symb_bound                   200
% 1.17/0.94  --lt_threshold                          2000
% 1.17/0.94  --clause_weak_htbl                      true
% 1.17/0.94  --gc_record_bc_elim                     false
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing Options
% 1.17/0.94  
% 1.17/0.94  --preprocessing_flag                    true
% 1.17/0.94  --time_out_prep_mult                    0.1
% 1.17/0.94  --splitting_mode                        input
% 1.17/0.94  --splitting_grd                         true
% 1.17/0.94  --splitting_cvd                         false
% 1.17/0.94  --splitting_cvd_svl                     false
% 1.17/0.94  --splitting_nvd                         32
% 1.17/0.94  --sub_typing                            true
% 1.17/0.94  --prep_gs_sim                           true
% 1.17/0.94  --prep_unflatten                        true
% 1.17/0.94  --prep_res_sim                          true
% 1.17/0.94  --prep_upred                            true
% 1.17/0.94  --prep_sem_filter                       exhaustive
% 1.17/0.94  --prep_sem_filter_out                   false
% 1.17/0.94  --pred_elim                             true
% 1.17/0.94  --res_sim_input                         true
% 1.17/0.94  --eq_ax_congr_red                       true
% 1.17/0.94  --pure_diseq_elim                       true
% 1.17/0.94  --brand_transform                       false
% 1.17/0.94  --non_eq_to_eq                          false
% 1.17/0.94  --prep_def_merge                        true
% 1.17/0.94  --prep_def_merge_prop_impl              false
% 1.17/0.94  --prep_def_merge_mbd                    true
% 1.17/0.94  --prep_def_merge_tr_red                 false
% 1.17/0.94  --prep_def_merge_tr_cl                  false
% 1.17/0.94  --smt_preprocessing                     true
% 1.17/0.94  --smt_ac_axioms                         fast
% 1.17/0.94  --preprocessed_out                      false
% 1.17/0.94  --preprocessed_stats                    false
% 1.17/0.94  
% 1.17/0.94  ------ Abstraction refinement Options
% 1.17/0.94  
% 1.17/0.94  --abstr_ref                             []
% 1.17/0.94  --abstr_ref_prep                        false
% 1.17/0.94  --abstr_ref_until_sat                   false
% 1.17/0.94  --abstr_ref_sig_restrict                funpre
% 1.17/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/0.94  --abstr_ref_under                       []
% 1.17/0.94  
% 1.17/0.94  ------ SAT Options
% 1.17/0.94  
% 1.17/0.94  --sat_mode                              false
% 1.17/0.94  --sat_fm_restart_options                ""
% 1.17/0.94  --sat_gr_def                            false
% 1.17/0.94  --sat_epr_types                         true
% 1.17/0.94  --sat_non_cyclic_types                  false
% 1.17/0.94  --sat_finite_models                     false
% 1.17/0.94  --sat_fm_lemmas                         false
% 1.17/0.94  --sat_fm_prep                           false
% 1.17/0.94  --sat_fm_uc_incr                        true
% 1.17/0.94  --sat_out_model                         small
% 1.17/0.94  --sat_out_clauses                       false
% 1.17/0.94  
% 1.17/0.94  ------ QBF Options
% 1.17/0.94  
% 1.17/0.94  --qbf_mode                              false
% 1.17/0.94  --qbf_elim_univ                         false
% 1.17/0.94  --qbf_dom_inst                          none
% 1.17/0.94  --qbf_dom_pre_inst                      false
% 1.17/0.94  --qbf_sk_in                             false
% 1.17/0.94  --qbf_pred_elim                         true
% 1.17/0.94  --qbf_split                             512
% 1.17/0.94  
% 1.17/0.94  ------ BMC1 Options
% 1.17/0.94  
% 1.17/0.94  --bmc1_incremental                      false
% 1.17/0.94  --bmc1_axioms                           reachable_all
% 1.17/0.94  --bmc1_min_bound                        0
% 1.17/0.94  --bmc1_max_bound                        -1
% 1.17/0.94  --bmc1_max_bound_default                -1
% 1.17/0.94  --bmc1_symbol_reachability              true
% 1.17/0.94  --bmc1_property_lemmas                  false
% 1.17/0.94  --bmc1_k_induction                      false
% 1.17/0.94  --bmc1_non_equiv_states                 false
% 1.17/0.94  --bmc1_deadlock                         false
% 1.17/0.94  --bmc1_ucm                              false
% 1.17/0.94  --bmc1_add_unsat_core                   none
% 1.17/0.94  --bmc1_unsat_core_children              false
% 1.17/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/0.94  --bmc1_out_stat                         full
% 1.17/0.94  --bmc1_ground_init                      false
% 1.17/0.94  --bmc1_pre_inst_next_state              false
% 1.17/0.94  --bmc1_pre_inst_state                   false
% 1.17/0.94  --bmc1_pre_inst_reach_state             false
% 1.17/0.94  --bmc1_out_unsat_core                   false
% 1.17/0.94  --bmc1_aig_witness_out                  false
% 1.17/0.94  --bmc1_verbose                          false
% 1.17/0.94  --bmc1_dump_clauses_tptp                false
% 1.17/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.17/0.94  --bmc1_dump_file                        -
% 1.17/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.17/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.17/0.94  --bmc1_ucm_extend_mode                  1
% 1.17/0.94  --bmc1_ucm_init_mode                    2
% 1.17/0.94  --bmc1_ucm_cone_mode                    none
% 1.17/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.17/0.94  --bmc1_ucm_relax_model                  4
% 1.17/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.17/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/0.94  --bmc1_ucm_layered_model                none
% 1.17/0.94  --bmc1_ucm_max_lemma_size               10
% 1.17/0.94  
% 1.17/0.94  ------ AIG Options
% 1.17/0.94  
% 1.17/0.94  --aig_mode                              false
% 1.17/0.94  
% 1.17/0.94  ------ Instantiation Options
% 1.17/0.94  
% 1.17/0.94  --instantiation_flag                    true
% 1.17/0.94  --inst_sos_flag                         false
% 1.17/0.94  --inst_sos_phase                        true
% 1.17/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/0.94  --inst_lit_sel_side                     none
% 1.17/0.94  --inst_solver_per_active                1400
% 1.17/0.94  --inst_solver_calls_frac                1.
% 1.17/0.94  --inst_passive_queue_type               priority_queues
% 1.17/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/0.94  --inst_passive_queues_freq              [25;2]
% 1.17/0.94  --inst_dismatching                      true
% 1.17/0.94  --inst_eager_unprocessed_to_passive     true
% 1.17/0.94  --inst_prop_sim_given                   true
% 1.17/0.94  --inst_prop_sim_new                     false
% 1.17/0.94  --inst_subs_new                         false
% 1.17/0.94  --inst_eq_res_simp                      false
% 1.17/0.94  --inst_subs_given                       false
% 1.17/0.94  --inst_orphan_elimination               true
% 1.17/0.94  --inst_learning_loop_flag               true
% 1.17/0.94  --inst_learning_start                   3000
% 1.17/0.94  --inst_learning_factor                  2
% 1.17/0.94  --inst_start_prop_sim_after_learn       3
% 1.17/0.94  --inst_sel_renew                        solver
% 1.17/0.94  --inst_lit_activity_flag                true
% 1.17/0.94  --inst_restr_to_given                   false
% 1.17/0.94  --inst_activity_threshold               500
% 1.17/0.94  --inst_out_proof                        true
% 1.17/0.94  
% 1.17/0.94  ------ Resolution Options
% 1.17/0.94  
% 1.17/0.94  --resolution_flag                       false
% 1.17/0.94  --res_lit_sel                           adaptive
% 1.17/0.94  --res_lit_sel_side                      none
% 1.17/0.94  --res_ordering                          kbo
% 1.17/0.94  --res_to_prop_solver                    active
% 1.17/0.94  --res_prop_simpl_new                    false
% 1.17/0.94  --res_prop_simpl_given                  true
% 1.17/0.94  --res_passive_queue_type                priority_queues
% 1.17/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/0.94  --res_passive_queues_freq               [15;5]
% 1.17/0.94  --res_forward_subs                      full
% 1.17/0.94  --res_backward_subs                     full
% 1.17/0.94  --res_forward_subs_resolution           true
% 1.17/0.94  --res_backward_subs_resolution          true
% 1.17/0.94  --res_orphan_elimination                true
% 1.17/0.94  --res_time_limit                        2.
% 1.17/0.94  --res_out_proof                         true
% 1.17/0.94  
% 1.17/0.94  ------ Superposition Options
% 1.17/0.94  
% 1.17/0.94  --superposition_flag                    true
% 1.17/0.94  --sup_passive_queue_type                priority_queues
% 1.17/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.17/0.94  --demod_completeness_check              fast
% 1.17/0.94  --demod_use_ground                      true
% 1.17/0.94  --sup_to_prop_solver                    passive
% 1.17/0.94  --sup_prop_simpl_new                    true
% 1.17/0.94  --sup_prop_simpl_given                  true
% 1.17/0.94  --sup_fun_splitting                     false
% 1.17/0.94  --sup_smt_interval                      50000
% 1.17/0.94  
% 1.17/0.94  ------ Superposition Simplification Setup
% 1.17/0.94  
% 1.17/0.94  --sup_indices_passive                   []
% 1.17/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_full_bw                           [BwDemod]
% 1.17/0.94  --sup_immed_triv                        [TrivRules]
% 1.17/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_immed_bw_main                     []
% 1.17/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/0.94  
% 1.17/0.94  ------ Combination Options
% 1.17/0.94  
% 1.17/0.94  --comb_res_mult                         3
% 1.17/0.94  --comb_sup_mult                         2
% 1.17/0.94  --comb_inst_mult                        10
% 1.17/0.94  
% 1.17/0.94  ------ Debug Options
% 1.17/0.94  
% 1.17/0.94  --dbg_backtrace                         false
% 1.17/0.94  --dbg_dump_prop_clauses                 false
% 1.17/0.94  --dbg_dump_prop_clauses_file            -
% 1.17/0.94  --dbg_out_stat                          false
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  ------ Proving...
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  % SZS status Theorem for theBenchmark.p
% 1.17/0.94  
% 1.17/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/0.94  
% 1.17/0.94  fof(f6,axiom,(
% 1.17/0.94    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f17,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.17/0.94    inference(ennf_transformation,[],[f6])).
% 1.17/0.94  
% 1.17/0.94  fof(f18,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(flattening,[],[f17])).
% 1.17/0.94  
% 1.17/0.94  fof(f28,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(nnf_transformation,[],[f18])).
% 1.17/0.94  
% 1.17/0.94  fof(f29,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(rectify,[],[f28])).
% 1.17/0.94  
% 1.17/0.94  fof(f30,plain,(
% 1.17/0.94    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.17/0.94    introduced(choice_axiom,[])).
% 1.17/0.94  
% 1.17/0.94  fof(f31,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.17/0.94  
% 1.17/0.94  fof(f44,plain,(
% 1.17/0.94    ( ! [X2,X0,X1] : (k4_orders_2(X0,X1) = X2 | m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f31])).
% 1.17/0.94  
% 1.17/0.94  fof(f10,conjecture,(
% 1.17/0.94    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f11,negated_conjecture,(
% 1.17/0.94    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.17/0.94    inference(negated_conjecture,[],[f10])).
% 1.17/0.94  
% 1.17/0.94  fof(f24,plain,(
% 1.17/0.94    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.17/0.94    inference(ennf_transformation,[],[f11])).
% 1.17/0.94  
% 1.17/0.94  fof(f25,plain,(
% 1.17/0.94    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.17/0.94    inference(flattening,[],[f24])).
% 1.17/0.94  
% 1.17/0.94  fof(f35,plain,(
% 1.17/0.94    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))))) )),
% 1.17/0.94    introduced(choice_axiom,[])).
% 1.17/0.94  
% 1.17/0.94  fof(f34,plain,(
% 1.17/0.94    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.17/0.94    introduced(choice_axiom,[])).
% 1.17/0.94  
% 1.17/0.94  fof(f36,plain,(
% 1.17/0.94    (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.17/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f35,f34])).
% 1.17/0.94  
% 1.17/0.94  fof(f56,plain,(
% 1.17/0.94    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f55,plain,(
% 1.17/0.94    l1_orders_2(sK3)),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f51,plain,(
% 1.17/0.94    ~v2_struct_0(sK3)),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f52,plain,(
% 1.17/0.94    v3_orders_2(sK3)),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f53,plain,(
% 1.17/0.94    v4_orders_2(sK3)),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f54,plain,(
% 1.17/0.94    v5_orders_2(sK3)),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f43,plain,(
% 1.17/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f31])).
% 1.17/0.94  
% 1.17/0.94  fof(f58,plain,(
% 1.17/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(equality_resolution,[],[f43])).
% 1.17/0.94  
% 1.17/0.94  fof(f57,plain,(
% 1.17/0.94    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))),
% 1.17/0.94    inference(cnf_transformation,[],[f36])).
% 1.17/0.94  
% 1.17/0.94  fof(f9,axiom,(
% 1.17/0.94    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f12,plain,(
% 1.17/0.94    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.17/0.94    inference(rectify,[],[f9])).
% 1.17/0.94  
% 1.17/0.94  fof(f23,plain,(
% 1.17/0.94    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.17/0.94    inference(ennf_transformation,[],[f12])).
% 1.17/0.94  
% 1.17/0.94  fof(f32,plain,(
% 1.17/0.94    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 1.17/0.94    introduced(choice_axiom,[])).
% 1.17/0.94  
% 1.17/0.94  fof(f33,plain,(
% 1.17/0.94    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.17/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f32])).
% 1.17/0.94  
% 1.17/0.94  fof(f48,plain,(
% 1.17/0.94    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.17/0.94    inference(cnf_transformation,[],[f33])).
% 1.17/0.94  
% 1.17/0.94  fof(f1,axiom,(
% 1.17/0.94    v1_xboole_0(k1_xboole_0)),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f37,plain,(
% 1.17/0.94    v1_xboole_0(k1_xboole_0)),
% 1.17/0.94    inference(cnf_transformation,[],[f1])).
% 1.17/0.94  
% 1.17/0.94  fof(f5,axiom,(
% 1.17/0.94    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f16,plain,(
% 1.17/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.17/0.94    inference(ennf_transformation,[],[f5])).
% 1.17/0.94  
% 1.17/0.94  fof(f41,plain,(
% 1.17/0.94    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f16])).
% 1.17/0.94  
% 1.17/0.94  fof(f7,axiom,(
% 1.17/0.94    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f19,plain,(
% 1.17/0.94    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.17/0.94    inference(ennf_transformation,[],[f7])).
% 1.17/0.94  
% 1.17/0.94  fof(f20,plain,(
% 1.17/0.94    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(flattening,[],[f19])).
% 1.17/0.94  
% 1.17/0.94  fof(f46,plain,(
% 1.17/0.94    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f20])).
% 1.17/0.94  
% 1.17/0.94  fof(f45,plain,(
% 1.17/0.94    ( ! [X2,X0,X1] : (k4_orders_2(X0,X1) = X2 | ~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f31])).
% 1.17/0.94  
% 1.17/0.94  fof(f2,axiom,(
% 1.17/0.94    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f13,plain,(
% 1.17/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.17/0.94    inference(ennf_transformation,[],[f2])).
% 1.17/0.94  
% 1.17/0.94  fof(f26,plain,(
% 1.17/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.17/0.94    introduced(choice_axiom,[])).
% 1.17/0.94  
% 1.17/0.94  fof(f27,plain,(
% 1.17/0.94    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.17/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).
% 1.17/0.94  
% 1.17/0.94  fof(f38,plain,(
% 1.17/0.94    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.17/0.94    inference(cnf_transformation,[],[f27])).
% 1.17/0.94  
% 1.17/0.94  fof(f8,axiom,(
% 1.17/0.94    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f21,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.17/0.94    inference(ennf_transformation,[],[f8])).
% 1.17/0.94  
% 1.17/0.94  fof(f22,plain,(
% 1.17/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.17/0.94    inference(flattening,[],[f21])).
% 1.17/0.94  
% 1.17/0.94  fof(f47,plain,(
% 1.17/0.94    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.17/0.94    inference(cnf_transformation,[],[f22])).
% 1.17/0.94  
% 1.17/0.94  fof(f3,axiom,(
% 1.17/0.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.17/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.17/0.94  
% 1.17/0.94  fof(f39,plain,(
% 1.17/0.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.17/0.94    inference(cnf_transformation,[],[f3])).
% 1.17/0.94  
% 1.17/0.94  cnf(c_6,plain,
% 1.17/0.94      ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.17/0.94      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.17/0.94      | r2_hidden(sK1(X0,X1,X2),X2)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,X1) = X2 ),
% 1.17/0.94      inference(cnf_transformation,[],[f44]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_15,negated_conjecture,
% 1.17/0.94      ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
% 1.17/0.94      inference(cnf_transformation,[],[f56]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_267,plain,
% 1.17/0.94      ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.17/0.94      | r2_hidden(sK1(X0,X1,X2),X2)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,X1) = X2
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_268,plain,
% 1.17/0.94      ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.17/0.94      | r2_hidden(sK1(X0,sK4,X1),X1)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) = X1
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_267]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_16,negated_conjecture,
% 1.17/0.94      ( l1_orders_2(sK3) ),
% 1.17/0.94      inference(cnf_transformation,[],[f55]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_540,plain,
% 1.17/0.94      ( m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.17/0.94      | r2_hidden(sK1(X0,sK4,X1),X1)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) = X1
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK3 != X0 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_268,c_16]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_541,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | v2_struct_0(sK3)
% 1.17/0.94      | ~ v3_orders_2(sK3)
% 1.17/0.94      | ~ v4_orders_2(sK3)
% 1.17/0.94      | ~ v5_orders_2(sK3)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_540]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_20,negated_conjecture,
% 1.17/0.94      ( ~ v2_struct_0(sK3) ),
% 1.17/0.94      inference(cnf_transformation,[],[f51]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_19,negated_conjecture,
% 1.17/0.94      ( v3_orders_2(sK3) ),
% 1.17/0.94      inference(cnf_transformation,[],[f52]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_18,negated_conjecture,
% 1.17/0.94      ( v4_orders_2(sK3) ),
% 1.17/0.94      inference(cnf_transformation,[],[f53]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_17,negated_conjecture,
% 1.17/0.94      ( v5_orders_2(sK3) ),
% 1.17/0.94      inference(cnf_transformation,[],[f54]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_545,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(global_propositional_subsumption,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_541,c_20,c_19,c_18,c_17]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1098,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0 ),
% 1.17/0.94      inference(equality_resolution_simp,[status(thm)],[c_545]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1921,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_1098]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_7,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,X2)
% 1.17/0.94      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1) ),
% 1.17/0.94      inference(cnf_transformation,[],[f58]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_393,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,X2)
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != X2 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_394,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,sK4)
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_393]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_564,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,sK4)
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK3 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_394,c_16]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_565,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.17/0.94      | v2_struct_0(sK3)
% 1.17/0.94      | ~ v3_orders_2(sK3)
% 1.17/0.94      | ~ v4_orders_2(sK3)
% 1.17/0.94      | ~ v5_orders_2(sK3)
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_564]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_569,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(global_propositional_subsumption,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_565,c_20,c_19,c_18,c_17]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1094,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.17/0.94      inference(equality_resolution_simp,[status(thm)],[c_569]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1132,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4) | r2_hidden(X0,k4_orders_2(sK3,sK4)) ),
% 1.17/0.94      inference(prop_impl,[status(thm)],[c_1094]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1922,plain,
% 1.17/0.94      ( m2_orders_2(X0,sK3,sK4) != iProver_top
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(sK3,sK4)) = iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_14,negated_conjecture,
% 1.17/0.94      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
% 1.17/0.94      inference(cnf_transformation,[],[f57]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_13,plain,
% 1.17/0.94      ( ~ r2_hidden(X0,X1)
% 1.17/0.94      | k3_tarski(X1) != k1_xboole_0
% 1.17/0.94      | k1_xboole_0 = X0 ),
% 1.17/0.94      inference(cnf_transformation,[],[f48]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1926,plain,
% 1.17/0.94      ( k3_tarski(X0) != k1_xboole_0
% 1.17/0.94      | k1_xboole_0 = X1
% 1.17/0.94      | r2_hidden(X1,X0) != iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2342,plain,
% 1.17/0.94      ( k1_xboole_0 = X0
% 1.17/0.94      | r2_hidden(X0,k4_orders_2(sK3,sK4)) != iProver_top ),
% 1.17/0.94      inference(superposition,[status(thm)],[c_14,c_1926]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2399,plain,
% 1.17/0.94      ( k1_xboole_0 = X0 | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 1.17/0.94      inference(superposition,[status(thm)],[c_1922,c_2342]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2421,plain,
% 1.17/0.94      ( sK1(sK3,sK4,X0) = k1_xboole_0
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0) = iProver_top ),
% 1.17/0.94      inference(superposition,[status(thm)],[c_1921,c_2399]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2423,plain,
% 1.17/0.94      ( sK1(sK3,sK4,k1_xboole_0) = k1_xboole_0
% 1.17/0.94      | k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2421]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1592,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.17/0.94      theory(equality) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2027,plain,
% 1.17/0.94      ( m1_subset_1(X0,X1)
% 1.17/0.94      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 1.17/0.94      | X1 != k1_zfmisc_1(X2)
% 1.17/0.94      | X0 != k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_1592]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2057,plain,
% 1.17/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.17/0.94      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 1.17/0.94      | X0 != k1_xboole_0
% 1.17/0.94      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2027]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2303,plain,
% 1.17/0.94      ( m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(X1))
% 1.17/0.94      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 1.17/0.94      | sK1(sK3,sK4,X0) != k1_xboole_0
% 1.17/0.94      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2057]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2305,plain,
% 1.17/0.94      ( m1_subset_1(sK1(sK3,sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | sK1(sK3,sK4,k1_xboole_0) != k1_xboole_0
% 1.17/0.94      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2303]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_0,plain,
% 1.17/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 1.17/0.94      inference(cnf_transformation,[],[f37]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_4,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.17/0.94      | ~ r2_hidden(X2,X0)
% 1.17/0.94      | ~ v1_xboole_0(X1) ),
% 1.17/0.94      inference(cnf_transformation,[],[f41]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_218,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.17/0.94      | ~ r2_hidden(X2,X0)
% 1.17/0.94      | k1_xboole_0 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_219,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_218]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2098,plain,
% 1.17/0.94      ( ~ m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | ~ r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,X0)) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_219]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2100,plain,
% 1.17/0.94      ( ~ m1_subset_1(sK1(sK3,sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | ~ r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k1_xboole_0)) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2098]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1591,plain,
% 1.17/0.94      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 1.17/0.94      theory(equality) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1600,plain,
% 1.17/0.94      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 1.17/0.94      | k1_xboole_0 != k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_1591]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_9,plain,
% 1.17/0.94      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 1.17/0.94      inference(cnf_transformation,[],[f46]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_230,plain,
% 1.17/0.94      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | k4_orders_2(X1,X0) != k1_xboole_0 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_423,plain,
% 1.17/0.94      ( v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,X1) != k1_xboole_0
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_230,c_15]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_424,plain,
% 1.17/0.94      ( v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) != k1_xboole_0
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_423]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_505,plain,
% 1.17/0.94      ( v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) != k1_xboole_0
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK3 != X0 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_424,c_16]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_506,plain,
% 1.17/0.94      ( v2_struct_0(sK3)
% 1.17/0.94      | ~ v3_orders_2(sK3)
% 1.17/0.94      | ~ v4_orders_2(sK3)
% 1.17/0.94      | ~ v5_orders_2(sK3)
% 1.17/0.94      | k4_orders_2(sK3,sK4) != k1_xboole_0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_505]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_508,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) != k1_xboole_0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(global_propositional_subsumption,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_506,c_20,c_19,c_18,c_17]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1106,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) != k1_xboole_0 ),
% 1.17/0.94      inference(equality_resolution_simp,[status(thm)],[c_508]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_5,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.17/0.94      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.17/0.94      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,X1) = X2 ),
% 1.17/0.94      inference(cnf_transformation,[],[f45]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_300,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
% 1.17/0.94      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,X1) = X2
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_301,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(X0,sK4,X1),X1)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | ~ l1_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) = X1
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_300]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_516,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(X0,sK4,X1),X0,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(X0,sK4,X1),X1)
% 1.17/0.94      | v2_struct_0(X0)
% 1.17/0.94      | ~ v3_orders_2(X0)
% 1.17/0.94      | ~ v4_orders_2(X0)
% 1.17/0.94      | ~ v5_orders_2(X0)
% 1.17/0.94      | k4_orders_2(X0,sK4) = X1
% 1.17/0.94      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK3 != X0 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_301,c_16]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_517,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | v2_struct_0(sK3)
% 1.17/0.94      | ~ v3_orders_2(sK3)
% 1.17/0.94      | ~ v4_orders_2(sK3)
% 1.17/0.94      | ~ v5_orders_2(sK3)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_516]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_521,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(global_propositional_subsumption,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_517,c_20,c_19,c_18,c_17]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1102,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0 ),
% 1.17/0.94      inference(equality_resolution_simp,[status(thm)],[c_521]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1103,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) != iProver_top
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,X0),X0) != iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1105,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.17/0.94      | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) != iProver_top
% 1.17/0.94      | r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_1103]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1104,plain,
% 1.17/0.94      ( ~ m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
% 1.17/0.94      | ~ r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0)
% 1.17/0.94      | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_1102]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_898,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | X0 != X1
% 1.17/0.94      | sK1(sK3,sK4,X0) != X2
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_219,c_545]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_899,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4)
% 1.17/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0 ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_898]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_900,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | m2_orders_2(sK1(sK3,sK4,X0),sK3,sK4) = iProver_top
% 1.17/0.94      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_902,plain,
% 1.17/0.94      ( k4_orders_2(sK3,sK4) = k1_xboole_0
% 1.17/0.94      | m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4) = iProver_top
% 1.17/0.94      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_900]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_901,plain,
% 1.17/0.94      ( m2_orders_2(sK1(sK3,sK4,k1_xboole_0),sK3,sK4)
% 1.17/0.94      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_899]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_1,plain,
% 1.17/0.94      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.17/0.94      inference(cnf_transformation,[],[f38]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_741,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | X0 != X1
% 1.17/0.94      | sK0(X1) != X2
% 1.17/0.94      | k1_xboole_0 = X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_219]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_742,plain,
% 1.17/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_741]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_744,plain,
% 1.17/0.94      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.17/0.94      | k1_xboole_0 = k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_742]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_10,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,X2)
% 1.17/0.94      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.17/0.94      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1) ),
% 1.17/0.94      inference(cnf_transformation,[],[f47]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_333,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,X2)
% 1.17/0.94      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != X2 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_334,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,sK4)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | ~ l1_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_333]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_606,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,X1,sK4)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 1.17/0.94      | v2_struct_0(X1)
% 1.17/0.94      | ~ v3_orders_2(X1)
% 1.17/0.94      | ~ v4_orders_2(X1)
% 1.17/0.94      | ~ v5_orders_2(X1)
% 1.17/0.94      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK3 != X1 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_334,c_16]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_607,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.17/0.94      | v2_struct_0(sK3)
% 1.17/0.94      | ~ v3_orders_2(sK3)
% 1.17/0.94      | ~ v4_orders_2(sK3)
% 1.17/0.94      | ~ v5_orders_2(sK3)
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_606]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_611,plain,
% 1.17/0.94      ( ~ m2_orders_2(X0,sK3,sK4)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 1.17/0.94      inference(global_propositional_subsumption,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_607,c_20,c_19,c_18,c_17]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_667,plain,
% 1.17/0.94      ( r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X1)
% 1.17/0.94      | sK1(sK3,sK4,X0) != X1
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0
% 1.17/0.94      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
% 1.17/0.94      | sK4 != sK4
% 1.17/0.94      | sK3 != sK3 ),
% 1.17/0.94      inference(resolution_lifted,[status(thm)],[c_545,c_611]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_668,plain,
% 1.17/0.94      ( r2_hidden(sK1(sK3,sK4,X0),X0)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,X0))
% 1.17/0.94      | k4_orders_2(sK3,sK4) = X0 ),
% 1.17/0.94      inference(unflattening,[status(thm)],[c_667]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_670,plain,
% 1.17/0.94      ( r2_hidden(sK1(sK3,sK4,k1_xboole_0),k1_xboole_0)
% 1.17/0.94      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),sK1(sK3,sK4,k1_xboole_0))
% 1.17/0.94      | k4_orders_2(sK3,sK4) = k1_xboole_0 ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_668]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_2,plain,
% 1.17/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.17/0.94      inference(cnf_transformation,[],[f39]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_58,plain,
% 1.17/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.17/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_60,plain,
% 1.17/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_58]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(c_59,plain,
% 1.17/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.17/0.94      inference(instantiation,[status(thm)],[c_2]) ).
% 1.17/0.94  
% 1.17/0.94  cnf(contradiction,plain,
% 1.17/0.94      ( $false ),
% 1.17/0.94      inference(minisat,
% 1.17/0.94                [status(thm)],
% 1.17/0.94                [c_2423,c_2305,c_2100,c_1600,c_1106,c_1105,c_1104,c_902,
% 1.17/0.94                 c_901,c_744,c_670,c_60,c_59]) ).
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/0.94  
% 1.17/0.94  ------                               Statistics
% 1.17/0.94  
% 1.17/0.94  ------ General
% 1.17/0.94  
% 1.17/0.94  abstr_ref_over_cycles:                  0
% 1.17/0.94  abstr_ref_under_cycles:                 0
% 1.17/0.94  gc_basic_clause_elim:                   0
% 1.17/0.94  forced_gc_time:                         0
% 1.17/0.94  parsing_time:                           0.01
% 1.17/0.94  unif_index_cands_time:                  0.
% 1.17/0.94  unif_index_add_time:                    0.
% 1.17/0.94  orderings_time:                         0.
% 1.17/0.94  out_proof_time:                         0.012
% 1.17/0.94  total_time:                             0.104
% 1.17/0.94  num_of_symbols:                         53
% 1.17/0.94  num_of_terms:                           1269
% 1.17/0.94  
% 1.17/0.94  ------ Preprocessing
% 1.17/0.94  
% 1.17/0.94  num_of_splits:                          0
% 1.17/0.94  num_of_split_atoms:                     0
% 1.17/0.94  num_of_reused_defs:                     0
% 1.17/0.94  num_eq_ax_congr_red:                    15
% 1.17/0.94  num_of_sem_filtered_clauses:            1
% 1.17/0.94  num_of_subtypes:                        0
% 1.17/0.94  monotx_restored_types:                  0
% 1.17/0.94  sat_num_of_epr_types:                   0
% 1.17/0.94  sat_num_of_non_cyclic_types:            0
% 1.17/0.94  sat_guarded_non_collapsed_types:        0
% 1.17/0.94  num_pure_diseq_elim:                    0
% 1.17/0.94  simp_replaced_by:                       0
% 1.17/0.94  res_preprocessed:                       86
% 1.17/0.94  prep_upred:                             0
% 1.17/0.94  prep_unflattend:                        105
% 1.17/0.94  smt_new_axioms:                         0
% 1.17/0.94  pred_elim_cands:                        3
% 1.17/0.94  pred_elim:                              7
% 1.17/0.94  pred_elim_cl:                           7
% 1.17/0.94  pred_elim_cycles:                       11
% 1.17/0.94  merged_defs:                            6
% 1.17/0.94  merged_defs_ncl:                        0
% 1.17/0.94  bin_hyper_res:                          6
% 1.17/0.94  prep_cycles:                            4
% 1.17/0.94  pred_elim_time:                         0.028
% 1.17/0.94  splitting_time:                         0.
% 1.17/0.94  sem_filter_time:                        0.
% 1.17/0.94  monotx_time:                            0.
% 1.17/0.94  subtype_inf_time:                       0.
% 1.17/0.94  
% 1.17/0.94  ------ Problem properties
% 1.17/0.94  
% 1.17/0.94  clauses:                                14
% 1.17/0.94  conjectures:                            1
% 1.17/0.94  epr:                                    0
% 1.17/0.94  horn:                                   11
% 1.17/0.94  ground:                                 2
% 1.17/0.94  unary:                                  3
% 1.17/0.94  binary:                                 7
% 1.17/0.94  lits:                                   29
% 1.17/0.94  lits_eq:                                10
% 1.17/0.94  fd_pure:                                0
% 1.17/0.94  fd_pseudo:                              0
% 1.17/0.94  fd_cond:                                4
% 1.17/0.94  fd_pseudo_cond:                         0
% 1.17/0.94  ac_symbols:                             0
% 1.17/0.94  
% 1.17/0.94  ------ Propositional Solver
% 1.17/0.94  
% 1.17/0.94  prop_solver_calls:                      25
% 1.17/0.94  prop_fast_solver_calls:                 737
% 1.17/0.94  smt_solver_calls:                       0
% 1.17/0.94  smt_fast_solver_calls:                  0
% 1.17/0.94  prop_num_of_clauses:                    488
% 1.17/0.94  prop_preprocess_simplified:             2779
% 1.17/0.94  prop_fo_subsumed:                       24
% 1.17/0.94  prop_solver_time:                       0.
% 1.17/0.94  smt_solver_time:                        0.
% 1.17/0.94  smt_fast_solver_time:                   0.
% 1.17/0.94  prop_fast_solver_time:                  0.
% 1.17/0.94  prop_unsat_core_time:                   0.
% 1.17/0.94  
% 1.17/0.94  ------ QBF
% 1.17/0.94  
% 1.17/0.94  qbf_q_res:                              0
% 1.17/0.94  qbf_num_tautologies:                    0
% 1.17/0.94  qbf_prep_cycles:                        0
% 1.17/0.94  
% 1.17/0.94  ------ BMC1
% 1.17/0.94  
% 1.17/0.94  bmc1_current_bound:                     -1
% 1.17/0.94  bmc1_last_solved_bound:                 -1
% 1.17/0.94  bmc1_unsat_core_size:                   -1
% 1.17/0.94  bmc1_unsat_core_parents_size:           -1
% 1.17/0.94  bmc1_merge_next_fun:                    0
% 1.17/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.17/0.94  
% 1.17/0.94  ------ Instantiation
% 1.17/0.94  
% 1.17/0.94  inst_num_of_clauses:                    102
% 1.17/0.94  inst_num_in_passive:                    35
% 1.17/0.94  inst_num_in_active:                     59
% 1.17/0.94  inst_num_in_unprocessed:                8
% 1.17/0.94  inst_num_of_loops:                      70
% 1.17/0.94  inst_num_of_learning_restarts:          0
% 1.17/0.94  inst_num_moves_active_passive:          9
% 1.17/0.94  inst_lit_activity:                      0
% 1.17/0.94  inst_lit_activity_moves:                0
% 1.17/0.94  inst_num_tautologies:                   0
% 1.17/0.94  inst_num_prop_implied:                  0
% 1.17/0.94  inst_num_existing_simplified:           0
% 1.17/0.94  inst_num_eq_res_simplified:             0
% 1.17/0.94  inst_num_child_elim:                    0
% 1.17/0.94  inst_num_of_dismatching_blockings:      8
% 1.17/0.94  inst_num_of_non_proper_insts:           50
% 1.17/0.94  inst_num_of_duplicates:                 0
% 1.17/0.94  inst_inst_num_from_inst_to_res:         0
% 1.17/0.94  inst_dismatching_checking_time:         0.
% 1.17/0.94  
% 1.17/0.94  ------ Resolution
% 1.17/0.94  
% 1.17/0.94  res_num_of_clauses:                     0
% 1.17/0.94  res_num_in_passive:                     0
% 1.17/0.94  res_num_in_active:                      0
% 1.17/0.94  res_num_of_loops:                       90
% 1.17/0.94  res_forward_subset_subsumed:            8
% 1.17/0.94  res_backward_subset_subsumed:           0
% 1.17/0.94  res_forward_subsumed:                   0
% 1.17/0.94  res_backward_subsumed:                  0
% 1.17/0.94  res_forward_subsumption_resolution:     0
% 1.17/0.94  res_backward_subsumption_resolution:    0
% 1.17/0.94  res_clause_to_clause_subsumption:       50
% 1.17/0.94  res_orphan_elimination:                 0
% 1.17/0.94  res_tautology_del:                      26
% 1.17/0.94  res_num_eq_res_simplified:              6
% 1.17/0.94  res_num_sel_changes:                    0
% 1.17/0.94  res_moves_from_active_to_pass:          0
% 1.17/0.94  
% 1.17/0.94  ------ Superposition
% 1.17/0.94  
% 1.17/0.94  sup_time_total:                         0.
% 1.17/0.94  sup_time_generating:                    0.
% 1.17/0.94  sup_time_sim_full:                      0.
% 1.17/0.94  sup_time_sim_immed:                     0.
% 1.17/0.94  
% 1.17/0.94  sup_num_of_clauses:                     22
% 1.17/0.94  sup_num_in_active:                      14
% 1.17/0.94  sup_num_in_passive:                     8
% 1.17/0.94  sup_num_of_loops:                       13
% 1.17/0.94  sup_fw_superposition:                   12
% 1.17/0.94  sup_bw_superposition:                   1
% 1.17/0.94  sup_immediate_simplified:               2
% 1.17/0.94  sup_given_eliminated:                   0
% 1.17/0.94  comparisons_done:                       0
% 1.17/0.94  comparisons_avoided:                    0
% 1.17/0.94  
% 1.17/0.94  ------ Simplifications
% 1.17/0.94  
% 1.17/0.94  
% 1.17/0.94  sim_fw_subset_subsumed:                 0
% 1.17/0.94  sim_bw_subset_subsumed:                 0
% 1.17/0.94  sim_fw_subsumed:                        0
% 1.17/0.94  sim_bw_subsumed:                        0
% 1.17/0.94  sim_fw_subsumption_res:                 0
% 1.17/0.94  sim_bw_subsumption_res:                 0
% 1.17/0.94  sim_tautology_del:                      2
% 1.17/0.94  sim_eq_tautology_del:                   4
% 1.17/0.94  sim_eq_res_simp:                        0
% 1.17/0.94  sim_fw_demodulated:                     2
% 1.17/0.94  sim_bw_demodulated:                     0
% 1.17/0.94  sim_light_normalised:                   0
% 1.17/0.94  sim_joinable_taut:                      0
% 1.17/0.94  sim_joinable_simp:                      0
% 1.17/0.94  sim_ac_normalised:                      0
% 1.17/0.94  sim_smt_subsumption:                    0
% 1.17/0.94  
%------------------------------------------------------------------------------
