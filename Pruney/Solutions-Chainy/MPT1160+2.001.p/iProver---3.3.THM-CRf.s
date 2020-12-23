%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:30 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 297 expanded)
%              Number of clauses        :   66 (  90 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  450 (1391 expanded)
%              Number of equality atoms :   66 ( 236 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1)
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f57,f56])).

fof(f88,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_699,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_698,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4104,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_699,c_698])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_336,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_481,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_27])).

cnf(c_482,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_4102,plain,
    ( X0 != k1_xboole_0
    | k1_struct_0(sK3) = X0 ),
    inference(resolution,[status(thm)],[c_699,c_482])).

cnf(c_6559,plain,
    ( X0 = k1_struct_0(sK3)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4104,c_4102])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_48,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_54,plain,
    ( ~ l1_struct_0(sK3)
    | k1_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_83,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_707,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_715,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1287,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1332,plain,
    ( ~ r1_tarski(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k3_orders_2(sK3,k1_struct_0(sK3),sK4))
    | k1_xboole_0 = k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1408,plain,
    ( r1_tarski(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0)
    | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK3,X2,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK3,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_31,c_30,c_29,c_27])).

cnf(c_1518,plain,
    ( ~ m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),u1_struct_0(sK3))
    | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4))
    | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1533,plain,
    ( r1_tarski(k1_xboole_0,k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_703,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1657,plain,
    ( X0 != u1_struct_0(sK3)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_2062,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1354,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1449,plain,
    ( m1_subset_1(k1_struct_0(sK3),X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_zfmisc_1(X1)
    | k1_struct_0(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1642,plain,
    ( m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_struct_0(sK3) != k1_xboole_0
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_2133,plain,
    ( m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_struct_0(sK3) != k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k3_orders_2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k3_orders_2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_31,c_30,c_29,c_27])).

cnf(c_2134,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_2264,plain,
    ( m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2406,plain,
    ( ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(X0))
    | m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
    | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3480,plain,
    ( ~ m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),u1_struct_0(sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_702,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_4083,plain,
    ( r1_tarski(k1_struct_0(sK3),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_702,c_482])).

cnf(c_700,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6282,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2422,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
    | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7576,plain,
    ( ~ r1_tarski(k1_struct_0(sK3),X0)
    | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
    | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_7672,plain,
    ( X0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6559,c_27,c_26,c_25,c_48,c_54,c_9,c_83,c_87,c_5,c_715,c_1287,c_1332,c_1408,c_1518,c_1533,c_2062,c_2133,c_2264,c_2406,c_3480,c_4083,c_6282,c_7576])).

cnf(c_7679,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7672,c_482])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.47/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.99  
% 3.47/0.99  ------  iProver source info
% 3.47/0.99  
% 3.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.99  git: non_committed_changes: false
% 3.47/0.99  git: last_make_outside_of_git: false
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  ------ Parsing...
% 3.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.99  
% 3.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.99  ------ Proving...
% 3.47/0.99  ------ Problem Properties 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  clauses                                 23
% 3.47/0.99  conjectures                             2
% 3.47/0.99  EPR                                     8
% 3.47/0.99  Horn                                    17
% 3.47/0.99  unary                                   7
% 3.47/0.99  binary                                  5
% 3.47/0.99  lits                                    56
% 3.47/0.99  lits eq                                 3
% 3.47/0.99  fd_pure                                 0
% 3.47/0.99  fd_pseudo                               0
% 3.47/0.99  fd_cond                                 0
% 3.47/0.99  fd_pseudo_cond                          1
% 3.47/0.99  AC symbols                              0
% 3.47/0.99  
% 3.47/0.99  ------ Input Options Time Limit: Unbounded
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ 
% 3.47/0.99  Current options:
% 3.47/0.99  ------ 
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  ------ Proving...
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS status Theorem for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99   Resolution empty clause
% 3.47/0.99  
% 3.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  fof(f16,axiom,(
% 3.47/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f36,plain,(
% 3.47/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f16])).
% 3.47/0.99  
% 3.47/0.99  fof(f80,plain,(
% 3.47/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f36])).
% 3.47/0.99  
% 3.47/0.99  fof(f14,axiom,(
% 3.47/0.99    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f33,plain,(
% 3.47/0.99    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.47/0.99    inference(ennf_transformation,[],[f14])).
% 3.47/0.99  
% 3.47/0.99  fof(f78,plain,(
% 3.47/0.99    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f33])).
% 3.47/0.99  
% 3.47/0.99  fof(f18,conjecture,(
% 3.47/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f19,negated_conjecture,(
% 3.47/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 3.47/0.99    inference(negated_conjecture,[],[f18])).
% 3.47/0.99  
% 3.47/0.99  fof(f39,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f19])).
% 3.47/0.99  
% 3.47/0.99  fof(f40,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f39])).
% 3.47/0.99  
% 3.47/0.99  fof(f57,plain,(
% 3.47/0.99    ( ! [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK4) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f56,plain,(
% 3.47/0.99    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f58,plain,(
% 3.47/0.99    (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f57,f56])).
% 3.47/0.99  
% 3.47/0.99  fof(f88,plain,(
% 3.47/0.99    l1_orders_2(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f89,plain,(
% 3.47/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f90,plain,(
% 3.47/0.99    k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f5,axiom,(
% 3.47/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f68,plain,(
% 3.47/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f5])).
% 3.47/0.99  
% 3.47/0.99  fof(f4,axiom,(
% 3.47/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f49,plain,(
% 3.47/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.99    inference(nnf_transformation,[],[f4])).
% 3.47/0.99  
% 3.47/0.99  fof(f50,plain,(
% 3.47/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.99    inference(flattening,[],[f49])).
% 3.47/0.99  
% 3.47/0.99  fof(f65,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.47/0.99    inference(cnf_transformation,[],[f50])).
% 3.47/0.99  
% 3.47/0.99  fof(f92,plain,(
% 3.47/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.47/0.99    inference(equality_resolution,[],[f65])).
% 3.47/0.99  
% 3.47/0.99  fof(f67,plain,(
% 3.47/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f50])).
% 3.47/0.99  
% 3.47/0.99  fof(f3,axiom,(
% 3.47/0.99    v1_xboole_0(k1_xboole_0)),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f64,plain,(
% 3.47/0.99    v1_xboole_0(k1_xboole_0)),
% 3.47/0.99    inference(cnf_transformation,[],[f3])).
% 3.47/0.99  
% 3.47/0.99  fof(f6,axiom,(
% 3.47/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f69,plain,(
% 3.47/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.47/0.99    inference(cnf_transformation,[],[f6])).
% 3.47/0.99  
% 3.47/0.99  fof(f2,axiom,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f20,plain,(
% 3.47/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f2])).
% 3.47/0.99  
% 3.47/0.99  fof(f45,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(nnf_transformation,[],[f20])).
% 3.47/0.99  
% 3.47/0.99  fof(f46,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(rectify,[],[f45])).
% 3.47/0.99  
% 3.47/0.99  fof(f47,plain,(
% 3.47/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f48,plain,(
% 3.47/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.47/0.99  
% 3.47/0.99  fof(f62,plain,(
% 3.47/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f48])).
% 3.47/0.99  
% 3.47/0.99  fof(f17,axiom,(
% 3.47/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f37,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f17])).
% 3.47/0.99  
% 3.47/0.99  fof(f38,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f37])).
% 3.47/0.99  
% 3.47/0.99  fof(f54,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(nnf_transformation,[],[f38])).
% 3.47/0.99  
% 3.47/0.99  fof(f55,plain,(
% 3.47/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f54])).
% 3.47/0.99  
% 3.47/0.99  fof(f82,plain,(
% 3.47/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f55])).
% 3.47/0.99  
% 3.47/0.99  fof(f87,plain,(
% 3.47/0.99    v5_orders_2(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f84,plain,(
% 3.47/0.99    ~v2_struct_0(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f85,plain,(
% 3.47/0.99    v3_orders_2(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f86,plain,(
% 3.47/0.99    v4_orders_2(sK3)),
% 3.47/0.99    inference(cnf_transformation,[],[f58])).
% 3.47/0.99  
% 3.47/0.99  fof(f15,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f34,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.47/0.99    inference(ennf_transformation,[],[f15])).
% 3.47/0.99  
% 3.47/0.99  fof(f35,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.47/0.99    inference(flattening,[],[f34])).
% 3.47/0.99  
% 3.47/0.99  fof(f79,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f35])).
% 3.47/0.99  
% 3.47/0.99  fof(f1,axiom,(
% 3.47/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f41,plain,(
% 3.47/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.47/0.99    inference(nnf_transformation,[],[f1])).
% 3.47/0.99  
% 3.47/0.99  fof(f42,plain,(
% 3.47/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.47/0.99    inference(rectify,[],[f41])).
% 3.47/0.99  
% 3.47/0.99  fof(f43,plain,(
% 3.47/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.47/0.99    introduced(choice_axiom,[])).
% 3.47/0.99  
% 3.47/0.99  fof(f44,plain,(
% 3.47/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.47/0.99  
% 3.47/0.99  fof(f59,plain,(
% 3.47/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f44])).
% 3.47/0.99  
% 3.47/0.99  fof(f9,axiom,(
% 3.47/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.47/0.99  
% 3.47/0.99  fof(f24,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.47/0.99    inference(ennf_transformation,[],[f9])).
% 3.47/0.99  
% 3.47/0.99  fof(f25,plain,(
% 3.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.47/0.99    inference(flattening,[],[f24])).
% 3.47/0.99  
% 3.47/0.99  fof(f72,plain,(
% 3.47/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f25])).
% 3.47/0.99  
% 3.47/0.99  fof(f61,plain,(
% 3.47/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.47/0.99    inference(cnf_transformation,[],[f48])).
% 3.47/0.99  
% 3.47/0.99  cnf(c_699,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_698,plain,( X0 = X0 ),theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4104,plain,
% 3.47/0.99      ( X0 != X1 | X1 = X0 ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_699,c_698]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_21,plain,
% 3.47/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_19,plain,
% 3.47/0.99      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_336,plain,
% 3.47/0.99      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_27,negated_conjecture,
% 3.47/0.99      ( l1_orders_2(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_481,plain,
% 3.47/0.99      ( k1_struct_0(X0) = k1_xboole_0 | sK3 != X0 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_336,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_482,plain,
% 3.47/0.99      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4102,plain,
% 3.47/0.99      ( X0 != k1_xboole_0 | k1_struct_0(sK3) = X0 ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_699,c_482]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6559,plain,
% 3.47/0.99      ( X0 = k1_struct_0(sK3) | X0 != k1_xboole_0 ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_4104,c_4102]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_26,negated_conjecture,
% 3.47/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_25,negated_conjecture,
% 3.47/0.99      ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
% 3.47/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_48,plain,
% 3.47/0.99      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_54,plain,
% 3.47/0.99      ( ~ l1_struct_0(sK3) | k1_struct_0(sK3) = k1_xboole_0 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_9,plain,
% 3.47/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_8,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f92]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_83,plain,
% 3.47/0.99      ( r1_tarski(sK3,sK3) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.47/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_87,plain,
% 3.47/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_5,plain,
% 3.47/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_707,plain,
% 3.47/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.47/0.99      theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_715,plain,
% 3.47/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_707]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_10,plain,
% 3.47/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.47/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1287,plain,
% 3.47/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1332,plain,
% 3.47/0.99      ( ~ r1_tarski(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0)
% 3.47/0.99      | ~ r1_tarski(k1_xboole_0,k3_orders_2(sK3,k1_struct_0(sK3),sK4))
% 3.47/0.99      | k1_xboole_0 = k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3,plain,
% 3.47/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.47/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1408,plain,
% 3.47/0.99      ( r1_tarski(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0)
% 3.47/0.99      | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_23,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | r2_hidden(X2,X3)
% 3.47/0.99      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ v3_orders_2(X1)
% 3.47/0.99      | ~ v4_orders_2(X1)
% 3.47/0.99      | ~ v5_orders_2(X1)
% 3.47/0.99      | ~ l1_orders_2(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_28,negated_conjecture,
% 3.47/0.99      ( v5_orders_2(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_416,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | r2_hidden(X2,X3)
% 3.47/0.99      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ v3_orders_2(X1)
% 3.47/0.99      | ~ v4_orders_2(X1)
% 3.47/0.99      | ~ l1_orders_2(X1)
% 3.47/0.99      | sK3 != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_417,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | r2_hidden(X1,X2)
% 3.47/0.99      | ~ r2_hidden(X1,k3_orders_2(sK3,X2,X0))
% 3.47/0.99      | v2_struct_0(sK3)
% 3.47/0.99      | ~ v3_orders_2(sK3)
% 3.47/0.99      | ~ v4_orders_2(sK3)
% 3.47/0.99      | ~ l1_orders_2(sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_31,negated_conjecture,
% 3.47/0.99      ( ~ v2_struct_0(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_30,negated_conjecture,
% 3.47/0.99      ( v3_orders_2(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_29,negated_conjecture,
% 3.47/0.99      ( v4_orders_2(sK3) ),
% 3.47/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_421,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | r2_hidden(X1,X2)
% 3.47/0.99      | ~ r2_hidden(X1,k3_orders_2(sK3,X2,X0)) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_417,c_31,c_30,c_29,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1518,plain,
% 3.47/0.99      ( ~ m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.47/0.99      | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4))
% 3.47/0.99      | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_421]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1533,plain,
% 3.47/0.99      ( r1_tarski(k1_xboole_0,k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_703,plain,
% 3.47/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.47/0.99      theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1657,plain,
% 3.47/0.99      ( X0 != u1_struct_0(sK3)
% 3.47/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_703]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2062,plain,
% 3.47/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.47/0.99      | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1657]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_704,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.47/0.99      theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1354,plain,
% 3.47/0.99      ( m1_subset_1(X0,X1)
% 3.47/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.47/0.99      | X1 != k1_zfmisc_1(X2)
% 3.47/0.99      | X0 != k1_xboole_0 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_704]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1449,plain,
% 3.47/0.99      ( m1_subset_1(k1_struct_0(sK3),X0)
% 3.47/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.47/0.99      | X0 != k1_zfmisc_1(X1)
% 3.47/0.99      | k1_struct_0(sK3) != k1_xboole_0 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1354]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1642,plain,
% 3.47/0.99      ( m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(X0))
% 3.47/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 3.47/0.99      | k1_struct_0(sK3) != k1_xboole_0
% 3.47/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1449]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2133,plain,
% 3.47/0.99      ( m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | k1_struct_0(sK3) != k1_xboole_0
% 3.47/0.99      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_20,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ v3_orders_2(X1)
% 3.47/0.99      | ~ v4_orders_2(X1)
% 3.47/0.99      | ~ v5_orders_2(X1)
% 3.47/0.99      | ~ l1_orders_2(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_443,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.47/0.99      | v2_struct_0(X1)
% 3.47/0.99      | ~ v3_orders_2(X1)
% 3.47/0.99      | ~ v4_orders_2(X1)
% 3.47/0.99      | ~ l1_orders_2(X1)
% 3.47/0.99      | sK3 != X1 ),
% 3.47/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_444,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | m1_subset_1(k3_orders_2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | v2_struct_0(sK3)
% 3.47/0.99      | ~ v3_orders_2(sK3)
% 3.47/0.99      | ~ v4_orders_2(sK3)
% 3.47/0.99      | ~ l1_orders_2(sK3) ),
% 3.47/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_448,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | m1_subset_1(k3_orders_2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_444,c_31,c_30,c_29,c_27]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2134,plain,
% 3.47/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.47/0.99      | m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_448]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2264,plain,
% 3.47/0.99      ( m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | ~ m1_subset_1(k1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_2134]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1,plain,
% 3.47/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2406,plain,
% 3.47/0.99      ( ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
% 3.47/0.99      | ~ v1_xboole_0(X0) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_13,plain,
% 3.47/0.99      ( m1_subset_1(X0,X1)
% 3.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.47/0.99      | ~ r2_hidden(X0,X2) ),
% 3.47/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_1508,plain,
% 3.47/0.99      ( ~ m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(X0))
% 3.47/0.99      | m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
% 3.47/0.99      | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_3480,plain,
% 3.47/0.99      ( ~ m1_subset_1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.47/0.99      | m1_subset_1(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),u1_struct_0(sK3))
% 3.47/0.99      | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k3_orders_2(sK3,k1_struct_0(sK3),sK4)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_702,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.47/0.99      theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4083,plain,
% 3.47/0.99      ( r1_tarski(k1_struct_0(sK3),X0) | ~ r1_tarski(k1_xboole_0,X0) ),
% 3.47/0.99      inference(resolution,[status(thm)],[c_702,c_482]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_700,plain,
% 3.47/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.47/0.99      theory(equality) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_6282,plain,
% 3.47/0.99      ( v1_xboole_0(X0) | ~ v1_xboole_0(k1_xboole_0) | X0 != k1_xboole_0 ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_700]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_4,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.47/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_2422,plain,
% 3.47/0.99      ( ~ r1_tarski(X0,X1)
% 3.47/0.99      | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
% 3.47/0.99      | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X1) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7576,plain,
% 3.47/0.99      ( ~ r1_tarski(k1_struct_0(sK3),X0)
% 3.47/0.99      | r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),X0)
% 3.47/0.99      | ~ r2_hidden(sK1(k3_orders_2(sK3,k1_struct_0(sK3),sK4),k1_xboole_0),k1_struct_0(sK3)) ),
% 3.47/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7672,plain,
% 3.47/0.99      ( X0 != k1_xboole_0 ),
% 3.47/0.99      inference(global_propositional_subsumption,
% 3.47/0.99                [status(thm)],
% 3.47/0.99                [c_6559,c_27,c_26,c_25,c_48,c_54,c_9,c_83,c_87,c_5,c_715,
% 3.47/0.99                 c_1287,c_1332,c_1408,c_1518,c_1533,c_2062,c_2133,c_2264,
% 3.47/0.99                 c_2406,c_3480,c_4083,c_6282,c_7576]) ).
% 3.47/0.99  
% 3.47/0.99  cnf(c_7679,plain,
% 3.47/0.99      ( $false ),
% 3.47/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_7672,c_482]) ).
% 3.47/0.99  
% 3.47/0.99  
% 3.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.99  
% 3.47/0.99  ------                               Statistics
% 3.47/0.99  
% 3.47/0.99  ------ Selected
% 3.47/0.99  
% 3.47/0.99  total_time:                             0.248
% 3.47/0.99  
%------------------------------------------------------------------------------
