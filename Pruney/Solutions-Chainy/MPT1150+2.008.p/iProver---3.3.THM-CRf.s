%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:06 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  140 (1294 expanded)
%              Number of clauses        :   84 ( 368 expanded)
%              Number of leaves         :   17 ( 281 expanded)
%              Depth                    :   20
%              Number of atoms          :  575 (6318 expanded)
%              Number of equality atoms :  170 (1194 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).

fof(f61,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_25,c_24,c_23,c_21])).

cnf(c_1137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_287,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_598,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_287,c_21])).

cnf(c_599,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_1203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1137,c_599])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1141,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1141])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_273,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_585,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_25])).

cnf(c_586,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_50,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_65,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_588,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_25,c_21,c_50,c_65])).

cnf(c_1132,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1150,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1132,c_599])).

cnf(c_2647,plain,
    ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_1150])).

cnf(c_2648,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2647])).

cnf(c_17,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_394,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_395,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_25,c_24,c_23,c_21])).

cnf(c_1139,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1237,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1139,c_599])).

cnf(c_10,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_603,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_604,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_1131,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1162,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1131,c_599])).

cnf(c_1685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1162])).

cnf(c_2000,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1685,c_1203])).

cnf(c_2657,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_2000])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1140,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_5])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_25,c_24,c_23,c_21])).

cnf(c_1133,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1167,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1133,c_599])).

cnf(c_1554,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1155,c_1167])).

cnf(c_2660,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2657,c_1554])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1302,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1303,plain,
    ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_1145,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_25,c_24,c_23,c_21])).

cnf(c_1136,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1196,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1136,c_599])).

cnf(c_1889,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1196])).

cnf(c_1897,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1889,c_1155])).

cnf(c_1901,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1145,c_1897])).

cnf(c_3035,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_2648])).

cnf(c_3077,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3035,c_1554])).

cnf(c_3037,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_2000])).

cnf(c_3068,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3037,c_1554])).

cnf(c_3082,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3077,c_3068])).

cnf(c_838,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1446,plain,
    ( k1_orders_2(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k1_orders_2(X0,X1) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1929,plain,
    ( k1_orders_2(X0,k2_struct_0(sK3)) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_3351,plain,
    ( k1_orders_2(X0,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_3353,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3351])).

cnf(c_837,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3352,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_3587,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_20,c_1303,c_3082,c_3353,c_3352])).

cnf(c_3592,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3587,c_1155])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.33/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.03  
% 2.33/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.03  
% 2.33/1.03  ------  iProver source info
% 2.33/1.03  
% 2.33/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.03  git: non_committed_changes: false
% 2.33/1.03  git: last_make_outside_of_git: false
% 2.33/1.03  
% 2.33/1.03  ------ 
% 2.33/1.03  
% 2.33/1.03  ------ Input Options
% 2.33/1.03  
% 2.33/1.03  --out_options                           all
% 2.33/1.03  --tptp_safe_out                         true
% 2.33/1.03  --problem_path                          ""
% 2.33/1.03  --include_path                          ""
% 2.33/1.03  --clausifier                            res/vclausify_rel
% 2.33/1.03  --clausifier_options                    --mode clausify
% 2.33/1.03  --stdin                                 false
% 2.33/1.03  --stats_out                             all
% 2.33/1.03  
% 2.33/1.03  ------ General Options
% 2.33/1.03  
% 2.33/1.03  --fof                                   false
% 2.33/1.03  --time_out_real                         305.
% 2.33/1.03  --time_out_virtual                      -1.
% 2.33/1.03  --symbol_type_check                     false
% 2.33/1.03  --clausify_out                          false
% 2.33/1.03  --sig_cnt_out                           false
% 2.33/1.03  --trig_cnt_out                          false
% 2.33/1.03  --trig_cnt_out_tolerance                1.
% 2.33/1.03  --trig_cnt_out_sk_spl                   false
% 2.33/1.03  --abstr_cl_out                          false
% 2.33/1.03  
% 2.33/1.03  ------ Global Options
% 2.33/1.03  
% 2.33/1.03  --schedule                              default
% 2.33/1.03  --add_important_lit                     false
% 2.33/1.03  --prop_solver_per_cl                    1000
% 2.33/1.03  --min_unsat_core                        false
% 2.33/1.03  --soft_assumptions                      false
% 2.33/1.03  --soft_lemma_size                       3
% 2.33/1.03  --prop_impl_unit_size                   0
% 2.33/1.03  --prop_impl_unit                        []
% 2.33/1.03  --share_sel_clauses                     true
% 2.33/1.03  --reset_solvers                         false
% 2.33/1.03  --bc_imp_inh                            [conj_cone]
% 2.33/1.03  --conj_cone_tolerance                   3.
% 2.33/1.03  --extra_neg_conj                        none
% 2.33/1.03  --large_theory_mode                     true
% 2.33/1.03  --prolific_symb_bound                   200
% 2.33/1.03  --lt_threshold                          2000
% 2.33/1.03  --clause_weak_htbl                      true
% 2.33/1.03  --gc_record_bc_elim                     false
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing Options
% 2.33/1.03  
% 2.33/1.03  --preprocessing_flag                    true
% 2.33/1.03  --time_out_prep_mult                    0.1
% 2.33/1.03  --splitting_mode                        input
% 2.33/1.03  --splitting_grd                         true
% 2.33/1.03  --splitting_cvd                         false
% 2.33/1.03  --splitting_cvd_svl                     false
% 2.33/1.03  --splitting_nvd                         32
% 2.33/1.03  --sub_typing                            true
% 2.33/1.03  --prep_gs_sim                           true
% 2.33/1.03  --prep_unflatten                        true
% 2.33/1.03  --prep_res_sim                          true
% 2.33/1.03  --prep_upred                            true
% 2.33/1.03  --prep_sem_filter                       exhaustive
% 2.33/1.03  --prep_sem_filter_out                   false
% 2.33/1.03  --pred_elim                             true
% 2.33/1.03  --res_sim_input                         true
% 2.33/1.03  --eq_ax_congr_red                       true
% 2.33/1.03  --pure_diseq_elim                       true
% 2.33/1.03  --brand_transform                       false
% 2.33/1.03  --non_eq_to_eq                          false
% 2.33/1.03  --prep_def_merge                        true
% 2.33/1.03  --prep_def_merge_prop_impl              false
% 2.33/1.03  --prep_def_merge_mbd                    true
% 2.33/1.03  --prep_def_merge_tr_red                 false
% 2.33/1.03  --prep_def_merge_tr_cl                  false
% 2.33/1.03  --smt_preprocessing                     true
% 2.33/1.03  --smt_ac_axioms                         fast
% 2.33/1.03  --preprocessed_out                      false
% 2.33/1.03  --preprocessed_stats                    false
% 2.33/1.03  
% 2.33/1.03  ------ Abstraction refinement Options
% 2.33/1.03  
% 2.33/1.03  --abstr_ref                             []
% 2.33/1.03  --abstr_ref_prep                        false
% 2.33/1.03  --abstr_ref_until_sat                   false
% 2.33/1.03  --abstr_ref_sig_restrict                funpre
% 2.33/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.03  --abstr_ref_under                       []
% 2.33/1.03  
% 2.33/1.03  ------ SAT Options
% 2.33/1.03  
% 2.33/1.03  --sat_mode                              false
% 2.33/1.03  --sat_fm_restart_options                ""
% 2.33/1.03  --sat_gr_def                            false
% 2.33/1.03  --sat_epr_types                         true
% 2.33/1.03  --sat_non_cyclic_types                  false
% 2.33/1.03  --sat_finite_models                     false
% 2.33/1.03  --sat_fm_lemmas                         false
% 2.33/1.03  --sat_fm_prep                           false
% 2.33/1.03  --sat_fm_uc_incr                        true
% 2.33/1.03  --sat_out_model                         small
% 2.33/1.03  --sat_out_clauses                       false
% 2.33/1.03  
% 2.33/1.03  ------ QBF Options
% 2.33/1.03  
% 2.33/1.03  --qbf_mode                              false
% 2.33/1.03  --qbf_elim_univ                         false
% 2.33/1.03  --qbf_dom_inst                          none
% 2.33/1.03  --qbf_dom_pre_inst                      false
% 2.33/1.03  --qbf_sk_in                             false
% 2.33/1.03  --qbf_pred_elim                         true
% 2.33/1.03  --qbf_split                             512
% 2.33/1.03  
% 2.33/1.03  ------ BMC1 Options
% 2.33/1.03  
% 2.33/1.03  --bmc1_incremental                      false
% 2.33/1.03  --bmc1_axioms                           reachable_all
% 2.33/1.03  --bmc1_min_bound                        0
% 2.33/1.03  --bmc1_max_bound                        -1
% 2.33/1.03  --bmc1_max_bound_default                -1
% 2.33/1.03  --bmc1_symbol_reachability              true
% 2.33/1.03  --bmc1_property_lemmas                  false
% 2.33/1.03  --bmc1_k_induction                      false
% 2.33/1.03  --bmc1_non_equiv_states                 false
% 2.33/1.03  --bmc1_deadlock                         false
% 2.33/1.03  --bmc1_ucm                              false
% 2.33/1.03  --bmc1_add_unsat_core                   none
% 2.33/1.03  --bmc1_unsat_core_children              false
% 2.33/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.03  --bmc1_out_stat                         full
% 2.33/1.03  --bmc1_ground_init                      false
% 2.33/1.03  --bmc1_pre_inst_next_state              false
% 2.33/1.03  --bmc1_pre_inst_state                   false
% 2.33/1.03  --bmc1_pre_inst_reach_state             false
% 2.33/1.03  --bmc1_out_unsat_core                   false
% 2.33/1.03  --bmc1_aig_witness_out                  false
% 2.33/1.03  --bmc1_verbose                          false
% 2.33/1.03  --bmc1_dump_clauses_tptp                false
% 2.33/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.03  --bmc1_dump_file                        -
% 2.33/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.03  --bmc1_ucm_extend_mode                  1
% 2.33/1.03  --bmc1_ucm_init_mode                    2
% 2.33/1.03  --bmc1_ucm_cone_mode                    none
% 2.33/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.03  --bmc1_ucm_relax_model                  4
% 2.33/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.03  --bmc1_ucm_layered_model                none
% 2.33/1.03  --bmc1_ucm_max_lemma_size               10
% 2.33/1.03  
% 2.33/1.03  ------ AIG Options
% 2.33/1.03  
% 2.33/1.03  --aig_mode                              false
% 2.33/1.03  
% 2.33/1.03  ------ Instantiation Options
% 2.33/1.03  
% 2.33/1.03  --instantiation_flag                    true
% 2.33/1.03  --inst_sos_flag                         false
% 2.33/1.03  --inst_sos_phase                        true
% 2.33/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.03  --inst_lit_sel_side                     num_symb
% 2.33/1.03  --inst_solver_per_active                1400
% 2.33/1.03  --inst_solver_calls_frac                1.
% 2.33/1.03  --inst_passive_queue_type               priority_queues
% 2.33/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.03  --inst_passive_queues_freq              [25;2]
% 2.33/1.03  --inst_dismatching                      true
% 2.33/1.03  --inst_eager_unprocessed_to_passive     true
% 2.33/1.03  --inst_prop_sim_given                   true
% 2.33/1.03  --inst_prop_sim_new                     false
% 2.33/1.03  --inst_subs_new                         false
% 2.33/1.03  --inst_eq_res_simp                      false
% 2.33/1.03  --inst_subs_given                       false
% 2.33/1.03  --inst_orphan_elimination               true
% 2.33/1.03  --inst_learning_loop_flag               true
% 2.33/1.03  --inst_learning_start                   3000
% 2.33/1.03  --inst_learning_factor                  2
% 2.33/1.03  --inst_start_prop_sim_after_learn       3
% 2.33/1.03  --inst_sel_renew                        solver
% 2.33/1.03  --inst_lit_activity_flag                true
% 2.33/1.03  --inst_restr_to_given                   false
% 2.33/1.03  --inst_activity_threshold               500
% 2.33/1.03  --inst_out_proof                        true
% 2.33/1.03  
% 2.33/1.03  ------ Resolution Options
% 2.33/1.03  
% 2.33/1.03  --resolution_flag                       true
% 2.33/1.03  --res_lit_sel                           adaptive
% 2.33/1.03  --res_lit_sel_side                      none
% 2.33/1.03  --res_ordering                          kbo
% 2.33/1.03  --res_to_prop_solver                    active
% 2.33/1.03  --res_prop_simpl_new                    false
% 2.33/1.03  --res_prop_simpl_given                  true
% 2.33/1.03  --res_passive_queue_type                priority_queues
% 2.33/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.03  --res_passive_queues_freq               [15;5]
% 2.33/1.03  --res_forward_subs                      full
% 2.33/1.03  --res_backward_subs                     full
% 2.33/1.03  --res_forward_subs_resolution           true
% 2.33/1.03  --res_backward_subs_resolution          true
% 2.33/1.03  --res_orphan_elimination                true
% 2.33/1.03  --res_time_limit                        2.
% 2.33/1.03  --res_out_proof                         true
% 2.33/1.03  
% 2.33/1.03  ------ Superposition Options
% 2.33/1.03  
% 2.33/1.03  --superposition_flag                    true
% 2.33/1.03  --sup_passive_queue_type                priority_queues
% 2.33/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.03  --demod_completeness_check              fast
% 2.33/1.03  --demod_use_ground                      true
% 2.33/1.03  --sup_to_prop_solver                    passive
% 2.33/1.03  --sup_prop_simpl_new                    true
% 2.33/1.03  --sup_prop_simpl_given                  true
% 2.33/1.03  --sup_fun_splitting                     false
% 2.33/1.03  --sup_smt_interval                      50000
% 2.33/1.03  
% 2.33/1.03  ------ Superposition Simplification Setup
% 2.33/1.03  
% 2.33/1.03  --sup_indices_passive                   []
% 2.33/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_full_bw                           [BwDemod]
% 2.33/1.03  --sup_immed_triv                        [TrivRules]
% 2.33/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_immed_bw_main                     []
% 2.33/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.03  
% 2.33/1.03  ------ Combination Options
% 2.33/1.03  
% 2.33/1.03  --comb_res_mult                         3
% 2.33/1.03  --comb_sup_mult                         2
% 2.33/1.03  --comb_inst_mult                        10
% 2.33/1.03  
% 2.33/1.03  ------ Debug Options
% 2.33/1.03  
% 2.33/1.03  --dbg_backtrace                         false
% 2.33/1.03  --dbg_dump_prop_clauses                 false
% 2.33/1.03  --dbg_dump_prop_clauses_file            -
% 2.33/1.03  --dbg_out_stat                          false
% 2.33/1.03  ------ Parsing...
% 2.33/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.03  ------ Proving...
% 2.33/1.03  ------ Problem Properties 
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  clauses                                 18
% 2.33/1.03  conjectures                             1
% 2.33/1.03  EPR                                     4
% 2.33/1.03  Horn                                    13
% 2.33/1.03  unary                                   5
% 2.33/1.03  binary                                  3
% 2.33/1.03  lits                                    46
% 2.33/1.03  lits eq                                 6
% 2.33/1.03  fd_pure                                 0
% 2.33/1.03  fd_pseudo                               0
% 2.33/1.03  fd_cond                                 1
% 2.33/1.03  fd_pseudo_cond                          0
% 2.33/1.03  AC symbols                              0
% 2.33/1.03  
% 2.33/1.03  ------ Schedule dynamic 5 is on 
% 2.33/1.03  
% 2.33/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  ------ 
% 2.33/1.03  Current options:
% 2.33/1.03  ------ 
% 2.33/1.03  
% 2.33/1.03  ------ Input Options
% 2.33/1.03  
% 2.33/1.03  --out_options                           all
% 2.33/1.03  --tptp_safe_out                         true
% 2.33/1.03  --problem_path                          ""
% 2.33/1.03  --include_path                          ""
% 2.33/1.03  --clausifier                            res/vclausify_rel
% 2.33/1.03  --clausifier_options                    --mode clausify
% 2.33/1.03  --stdin                                 false
% 2.33/1.03  --stats_out                             all
% 2.33/1.03  
% 2.33/1.03  ------ General Options
% 2.33/1.03  
% 2.33/1.03  --fof                                   false
% 2.33/1.03  --time_out_real                         305.
% 2.33/1.03  --time_out_virtual                      -1.
% 2.33/1.03  --symbol_type_check                     false
% 2.33/1.03  --clausify_out                          false
% 2.33/1.03  --sig_cnt_out                           false
% 2.33/1.03  --trig_cnt_out                          false
% 2.33/1.03  --trig_cnt_out_tolerance                1.
% 2.33/1.03  --trig_cnt_out_sk_spl                   false
% 2.33/1.03  --abstr_cl_out                          false
% 2.33/1.03  
% 2.33/1.03  ------ Global Options
% 2.33/1.03  
% 2.33/1.03  --schedule                              default
% 2.33/1.03  --add_important_lit                     false
% 2.33/1.03  --prop_solver_per_cl                    1000
% 2.33/1.03  --min_unsat_core                        false
% 2.33/1.03  --soft_assumptions                      false
% 2.33/1.03  --soft_lemma_size                       3
% 2.33/1.03  --prop_impl_unit_size                   0
% 2.33/1.03  --prop_impl_unit                        []
% 2.33/1.03  --share_sel_clauses                     true
% 2.33/1.03  --reset_solvers                         false
% 2.33/1.03  --bc_imp_inh                            [conj_cone]
% 2.33/1.03  --conj_cone_tolerance                   3.
% 2.33/1.03  --extra_neg_conj                        none
% 2.33/1.03  --large_theory_mode                     true
% 2.33/1.03  --prolific_symb_bound                   200
% 2.33/1.03  --lt_threshold                          2000
% 2.33/1.03  --clause_weak_htbl                      true
% 2.33/1.03  --gc_record_bc_elim                     false
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing Options
% 2.33/1.03  
% 2.33/1.03  --preprocessing_flag                    true
% 2.33/1.03  --time_out_prep_mult                    0.1
% 2.33/1.03  --splitting_mode                        input
% 2.33/1.03  --splitting_grd                         true
% 2.33/1.03  --splitting_cvd                         false
% 2.33/1.03  --splitting_cvd_svl                     false
% 2.33/1.03  --splitting_nvd                         32
% 2.33/1.03  --sub_typing                            true
% 2.33/1.03  --prep_gs_sim                           true
% 2.33/1.03  --prep_unflatten                        true
% 2.33/1.03  --prep_res_sim                          true
% 2.33/1.03  --prep_upred                            true
% 2.33/1.03  --prep_sem_filter                       exhaustive
% 2.33/1.03  --prep_sem_filter_out                   false
% 2.33/1.03  --pred_elim                             true
% 2.33/1.03  --res_sim_input                         true
% 2.33/1.03  --eq_ax_congr_red                       true
% 2.33/1.03  --pure_diseq_elim                       true
% 2.33/1.03  --brand_transform                       false
% 2.33/1.03  --non_eq_to_eq                          false
% 2.33/1.03  --prep_def_merge                        true
% 2.33/1.03  --prep_def_merge_prop_impl              false
% 2.33/1.03  --prep_def_merge_mbd                    true
% 2.33/1.03  --prep_def_merge_tr_red                 false
% 2.33/1.03  --prep_def_merge_tr_cl                  false
% 2.33/1.03  --smt_preprocessing                     true
% 2.33/1.03  --smt_ac_axioms                         fast
% 2.33/1.03  --preprocessed_out                      false
% 2.33/1.03  --preprocessed_stats                    false
% 2.33/1.03  
% 2.33/1.03  ------ Abstraction refinement Options
% 2.33/1.03  
% 2.33/1.03  --abstr_ref                             []
% 2.33/1.03  --abstr_ref_prep                        false
% 2.33/1.03  --abstr_ref_until_sat                   false
% 2.33/1.03  --abstr_ref_sig_restrict                funpre
% 2.33/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.03  --abstr_ref_under                       []
% 2.33/1.03  
% 2.33/1.03  ------ SAT Options
% 2.33/1.03  
% 2.33/1.03  --sat_mode                              false
% 2.33/1.03  --sat_fm_restart_options                ""
% 2.33/1.03  --sat_gr_def                            false
% 2.33/1.03  --sat_epr_types                         true
% 2.33/1.03  --sat_non_cyclic_types                  false
% 2.33/1.03  --sat_finite_models                     false
% 2.33/1.03  --sat_fm_lemmas                         false
% 2.33/1.03  --sat_fm_prep                           false
% 2.33/1.03  --sat_fm_uc_incr                        true
% 2.33/1.03  --sat_out_model                         small
% 2.33/1.03  --sat_out_clauses                       false
% 2.33/1.03  
% 2.33/1.03  ------ QBF Options
% 2.33/1.03  
% 2.33/1.03  --qbf_mode                              false
% 2.33/1.03  --qbf_elim_univ                         false
% 2.33/1.03  --qbf_dom_inst                          none
% 2.33/1.03  --qbf_dom_pre_inst                      false
% 2.33/1.03  --qbf_sk_in                             false
% 2.33/1.03  --qbf_pred_elim                         true
% 2.33/1.03  --qbf_split                             512
% 2.33/1.03  
% 2.33/1.03  ------ BMC1 Options
% 2.33/1.03  
% 2.33/1.03  --bmc1_incremental                      false
% 2.33/1.03  --bmc1_axioms                           reachable_all
% 2.33/1.03  --bmc1_min_bound                        0
% 2.33/1.03  --bmc1_max_bound                        -1
% 2.33/1.03  --bmc1_max_bound_default                -1
% 2.33/1.03  --bmc1_symbol_reachability              true
% 2.33/1.03  --bmc1_property_lemmas                  false
% 2.33/1.03  --bmc1_k_induction                      false
% 2.33/1.03  --bmc1_non_equiv_states                 false
% 2.33/1.03  --bmc1_deadlock                         false
% 2.33/1.03  --bmc1_ucm                              false
% 2.33/1.03  --bmc1_add_unsat_core                   none
% 2.33/1.03  --bmc1_unsat_core_children              false
% 2.33/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.03  --bmc1_out_stat                         full
% 2.33/1.03  --bmc1_ground_init                      false
% 2.33/1.03  --bmc1_pre_inst_next_state              false
% 2.33/1.03  --bmc1_pre_inst_state                   false
% 2.33/1.03  --bmc1_pre_inst_reach_state             false
% 2.33/1.03  --bmc1_out_unsat_core                   false
% 2.33/1.03  --bmc1_aig_witness_out                  false
% 2.33/1.03  --bmc1_verbose                          false
% 2.33/1.03  --bmc1_dump_clauses_tptp                false
% 2.33/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.03  --bmc1_dump_file                        -
% 2.33/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.03  --bmc1_ucm_extend_mode                  1
% 2.33/1.03  --bmc1_ucm_init_mode                    2
% 2.33/1.03  --bmc1_ucm_cone_mode                    none
% 2.33/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.03  --bmc1_ucm_relax_model                  4
% 2.33/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.03  --bmc1_ucm_layered_model                none
% 2.33/1.03  --bmc1_ucm_max_lemma_size               10
% 2.33/1.03  
% 2.33/1.03  ------ AIG Options
% 2.33/1.03  
% 2.33/1.03  --aig_mode                              false
% 2.33/1.03  
% 2.33/1.03  ------ Instantiation Options
% 2.33/1.03  
% 2.33/1.03  --instantiation_flag                    true
% 2.33/1.03  --inst_sos_flag                         false
% 2.33/1.03  --inst_sos_phase                        true
% 2.33/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.03  --inst_lit_sel_side                     none
% 2.33/1.03  --inst_solver_per_active                1400
% 2.33/1.03  --inst_solver_calls_frac                1.
% 2.33/1.03  --inst_passive_queue_type               priority_queues
% 2.33/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.03  --inst_passive_queues_freq              [25;2]
% 2.33/1.03  --inst_dismatching                      true
% 2.33/1.03  --inst_eager_unprocessed_to_passive     true
% 2.33/1.03  --inst_prop_sim_given                   true
% 2.33/1.03  --inst_prop_sim_new                     false
% 2.33/1.03  --inst_subs_new                         false
% 2.33/1.03  --inst_eq_res_simp                      false
% 2.33/1.03  --inst_subs_given                       false
% 2.33/1.03  --inst_orphan_elimination               true
% 2.33/1.03  --inst_learning_loop_flag               true
% 2.33/1.03  --inst_learning_start                   3000
% 2.33/1.03  --inst_learning_factor                  2
% 2.33/1.03  --inst_start_prop_sim_after_learn       3
% 2.33/1.03  --inst_sel_renew                        solver
% 2.33/1.03  --inst_lit_activity_flag                true
% 2.33/1.03  --inst_restr_to_given                   false
% 2.33/1.03  --inst_activity_threshold               500
% 2.33/1.03  --inst_out_proof                        true
% 2.33/1.03  
% 2.33/1.03  ------ Resolution Options
% 2.33/1.03  
% 2.33/1.03  --resolution_flag                       false
% 2.33/1.03  --res_lit_sel                           adaptive
% 2.33/1.03  --res_lit_sel_side                      none
% 2.33/1.03  --res_ordering                          kbo
% 2.33/1.03  --res_to_prop_solver                    active
% 2.33/1.03  --res_prop_simpl_new                    false
% 2.33/1.03  --res_prop_simpl_given                  true
% 2.33/1.03  --res_passive_queue_type                priority_queues
% 2.33/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.03  --res_passive_queues_freq               [15;5]
% 2.33/1.03  --res_forward_subs                      full
% 2.33/1.03  --res_backward_subs                     full
% 2.33/1.03  --res_forward_subs_resolution           true
% 2.33/1.03  --res_backward_subs_resolution          true
% 2.33/1.03  --res_orphan_elimination                true
% 2.33/1.03  --res_time_limit                        2.
% 2.33/1.03  --res_out_proof                         true
% 2.33/1.03  
% 2.33/1.03  ------ Superposition Options
% 2.33/1.03  
% 2.33/1.03  --superposition_flag                    true
% 2.33/1.03  --sup_passive_queue_type                priority_queues
% 2.33/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.03  --demod_completeness_check              fast
% 2.33/1.03  --demod_use_ground                      true
% 2.33/1.03  --sup_to_prop_solver                    passive
% 2.33/1.03  --sup_prop_simpl_new                    true
% 2.33/1.03  --sup_prop_simpl_given                  true
% 2.33/1.03  --sup_fun_splitting                     false
% 2.33/1.03  --sup_smt_interval                      50000
% 2.33/1.03  
% 2.33/1.03  ------ Superposition Simplification Setup
% 2.33/1.03  
% 2.33/1.03  --sup_indices_passive                   []
% 2.33/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_full_bw                           [BwDemod]
% 2.33/1.03  --sup_immed_triv                        [TrivRules]
% 2.33/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_immed_bw_main                     []
% 2.33/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.03  
% 2.33/1.03  ------ Combination Options
% 2.33/1.03  
% 2.33/1.03  --comb_res_mult                         3
% 2.33/1.03  --comb_sup_mult                         2
% 2.33/1.03  --comb_inst_mult                        10
% 2.33/1.03  
% 2.33/1.03  ------ Debug Options
% 2.33/1.03  
% 2.33/1.03  --dbg_backtrace                         false
% 2.33/1.03  --dbg_dump_prop_clauses                 false
% 2.33/1.03  --dbg_dump_prop_clauses_file            -
% 2.33/1.03  --dbg_out_stat                          false
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  ------ Proving...
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  % SZS status Theorem for theBenchmark.p
% 2.33/1.03  
% 2.33/1.03   Resolution empty clause
% 2.33/1.03  
% 2.33/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.03  
% 2.33/1.03  fof(f10,axiom,(
% 2.33/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f22,plain,(
% 2.33/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.33/1.03    inference(ennf_transformation,[],[f10])).
% 2.33/1.03  
% 2.33/1.03  fof(f23,plain,(
% 2.33/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.33/1.03    inference(flattening,[],[f22])).
% 2.33/1.03  
% 2.33/1.03  fof(f31,plain,(
% 2.33/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.33/1.03    inference(nnf_transformation,[],[f23])).
% 2.33/1.03  
% 2.33/1.03  fof(f32,plain,(
% 2.33/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.33/1.03    inference(rectify,[],[f31])).
% 2.33/1.03  
% 2.33/1.03  fof(f34,plain,(
% 2.33/1.03    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.33/1.03    introduced(choice_axiom,[])).
% 2.33/1.03  
% 2.33/1.03  fof(f33,plain,(
% 2.33/1.03    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.33/1.03    introduced(choice_axiom,[])).
% 2.33/1.03  
% 2.33/1.03  fof(f35,plain,(
% 2.33/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.33/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 2.33/1.03  
% 2.33/1.03  fof(f52,plain,(
% 2.33/1.03    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f35])).
% 2.33/1.03  
% 2.33/1.03  fof(f11,conjecture,(
% 2.33/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f12,negated_conjecture,(
% 2.33/1.03    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.33/1.03    inference(negated_conjecture,[],[f11])).
% 2.33/1.03  
% 2.33/1.03  fof(f24,plain,(
% 2.33/1.03    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.33/1.03    inference(ennf_transformation,[],[f12])).
% 2.33/1.03  
% 2.33/1.03  fof(f25,plain,(
% 2.33/1.03    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.33/1.03    inference(flattening,[],[f24])).
% 2.33/1.03  
% 2.33/1.03  fof(f36,plain,(
% 2.33/1.03    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.33/1.03    introduced(choice_axiom,[])).
% 2.33/1.03  
% 2.33/1.03  fof(f37,plain,(
% 2.33/1.03    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.33/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f36])).
% 2.33/1.03  
% 2.33/1.03  fof(f61,plain,(
% 2.33/1.03    v5_orders_2(sK3)),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f58,plain,(
% 2.33/1.03    ~v2_struct_0(sK3)),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f59,plain,(
% 2.33/1.03    v3_orders_2(sK3)),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f60,plain,(
% 2.33/1.03    v4_orders_2(sK3)),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f62,plain,(
% 2.33/1.03    l1_orders_2(sK3)),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f9,axiom,(
% 2.33/1.03    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f21,plain,(
% 2.33/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.33/1.03    inference(ennf_transformation,[],[f9])).
% 2.33/1.03  
% 2.33/1.03  fof(f51,plain,(
% 2.33/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f21])).
% 2.33/1.03  
% 2.33/1.03  fof(f5,axiom,(
% 2.33/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f15,plain,(
% 2.33/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.33/1.03    inference(ennf_transformation,[],[f5])).
% 2.33/1.03  
% 2.33/1.03  fof(f45,plain,(
% 2.33/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f15])).
% 2.33/1.03  
% 2.33/1.03  fof(f2,axiom,(
% 2.33/1.03    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f14,plain,(
% 2.33/1.03    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.33/1.03    inference(ennf_transformation,[],[f2])).
% 2.33/1.03  
% 2.33/1.03  fof(f28,plain,(
% 2.33/1.03    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.33/1.03    inference(nnf_transformation,[],[f14])).
% 2.33/1.03  
% 2.33/1.03  fof(f39,plain,(
% 2.33/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f28])).
% 2.33/1.03  
% 2.33/1.03  fof(f6,axiom,(
% 2.33/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f16,plain,(
% 2.33/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/1.03    inference(ennf_transformation,[],[f6])).
% 2.33/1.03  
% 2.33/1.03  fof(f17,plain,(
% 2.33/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/1.03    inference(flattening,[],[f16])).
% 2.33/1.03  
% 2.33/1.03  fof(f46,plain,(
% 2.33/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f17])).
% 2.33/1.03  
% 2.33/1.03  fof(f54,plain,(
% 2.33/1.03    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f35])).
% 2.33/1.03  
% 2.33/1.03  fof(f7,axiom,(
% 2.33/1.03    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f18,plain,(
% 2.33/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.33/1.03    inference(ennf_transformation,[],[f7])).
% 2.33/1.03  
% 2.33/1.03  fof(f29,plain,(
% 2.33/1.03    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.33/1.03    inference(nnf_transformation,[],[f18])).
% 2.33/1.03  
% 2.33/1.03  fof(f30,plain,(
% 2.33/1.03    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.33/1.03    inference(flattening,[],[f29])).
% 2.33/1.03  
% 2.33/1.03  fof(f48,plain,(
% 2.33/1.03    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f30])).
% 2.33/1.03  
% 2.33/1.03  fof(f64,plain,(
% 2.33/1.03    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.33/1.03    inference(equality_resolution,[],[f48])).
% 2.33/1.03  
% 2.33/1.03  fof(f4,axiom,(
% 2.33/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f44,plain,(
% 2.33/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.33/1.03    inference(cnf_transformation,[],[f4])).
% 2.33/1.03  
% 2.33/1.03  fof(f3,axiom,(
% 2.33/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f43,plain,(
% 2.33/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.33/1.03    inference(cnf_transformation,[],[f3])).
% 2.33/1.03  
% 2.33/1.03  fof(f8,axiom,(
% 2.33/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f19,plain,(
% 2.33/1.03    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.33/1.03    inference(ennf_transformation,[],[f8])).
% 2.33/1.03  
% 2.33/1.03  fof(f20,plain,(
% 2.33/1.03    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.33/1.03    inference(flattening,[],[f19])).
% 2.33/1.03  
% 2.33/1.03  fof(f50,plain,(
% 2.33/1.03    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f20])).
% 2.33/1.03  
% 2.33/1.03  fof(f63,plain,(
% 2.33/1.03    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 2.33/1.03    inference(cnf_transformation,[],[f37])).
% 2.33/1.03  
% 2.33/1.03  fof(f1,axiom,(
% 2.33/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.33/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.03  
% 2.33/1.03  fof(f13,plain,(
% 2.33/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.33/1.03    inference(ennf_transformation,[],[f1])).
% 2.33/1.03  
% 2.33/1.03  fof(f26,plain,(
% 2.33/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.33/1.03    introduced(choice_axiom,[])).
% 2.33/1.03  
% 2.33/1.03  fof(f27,plain,(
% 2.33/1.03    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.33/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).
% 2.33/1.03  
% 2.33/1.03  fof(f38,plain,(
% 2.33/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.33/1.03    inference(cnf_transformation,[],[f27])).
% 2.33/1.03  
% 2.33/1.03  fof(f53,plain,(
% 2.33/1.03    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.33/1.03    inference(cnf_transformation,[],[f35])).
% 2.33/1.03  
% 2.33/1.03  cnf(c_19,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ v5_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1) ),
% 2.33/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_22,negated_conjecture,
% 2.33/1.03      ( v5_orders_2(sK3) ),
% 2.33/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_445,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1)
% 2.33/1.03      | sK3 != X1 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_446,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 2.33/1.03      | ~ v3_orders_2(sK3)
% 2.33/1.03      | ~ v4_orders_2(sK3)
% 2.33/1.03      | ~ l1_orders_2(sK3)
% 2.33/1.03      | v2_struct_0(sK3) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_445]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_25,negated_conjecture,
% 2.33/1.03      ( ~ v2_struct_0(sK3) ),
% 2.33/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_24,negated_conjecture,
% 2.33/1.03      ( v3_orders_2(sK3) ),
% 2.33/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_23,negated_conjecture,
% 2.33/1.03      ( v4_orders_2(sK3) ),
% 2.33/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_21,negated_conjecture,
% 2.33/1.03      ( l1_orders_2(sK3) ),
% 2.33/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_450,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_446,c_25,c_24,c_23,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1137,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.33/1.03      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_13,plain,
% 2.33/1.03      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.33/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_7,plain,
% 2.33/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.33/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_287,plain,
% 2.33/1.03      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.33/1.03      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_598,plain,
% 2.33/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_287,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_599,plain,
% 2.33/1.03      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_598]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1203,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1137,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_4,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.33/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1141,plain,
% 2.33/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.33/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.33/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1560,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 2.33/1.03      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.33/1.03      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1203,c_1141]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_8,plain,
% 2.33/1.03      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.33/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_273,plain,
% 2.33/1.03      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.33/1.03      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_585,plain,
% 2.33/1.03      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_273,c_25]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_586,plain,
% 2.33/1.03      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_585]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_50,plain,
% 2.33/1.03      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_65,plain,
% 2.33/1.03      ( v2_struct_0(sK3)
% 2.33/1.03      | ~ l1_struct_0(sK3)
% 2.33/1.03      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_588,plain,
% 2.33/1.03      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_586,c_25,c_21,c_50,c_65]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1132,plain,
% 2.33/1.03      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1150,plain,
% 2.33/1.03      ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1132,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_2647,plain,
% 2.33/1.03      ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 2.33/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1560,c_1150]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_2648,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 2.33/1.03      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
% 2.33/1.03      inference(renaming,[status(thm)],[c_2647]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_17,plain,
% 2.33/1.03      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.33/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.03      | ~ r2_hidden(X1,X3)
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.33/1.03      | ~ v3_orders_2(X0)
% 2.33/1.03      | ~ v4_orders_2(X0)
% 2.33/1.03      | ~ v5_orders_2(X0)
% 2.33/1.03      | ~ l1_orders_2(X0)
% 2.33/1.03      | v2_struct_0(X0) ),
% 2.33/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_394,plain,
% 2.33/1.03      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.33/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/1.03      | ~ r2_hidden(X1,X3)
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.33/1.03      | ~ v3_orders_2(X0)
% 2.33/1.03      | ~ v4_orders_2(X0)
% 2.33/1.03      | ~ l1_orders_2(X0)
% 2.33/1.03      | v2_struct_0(X0)
% 2.33/1.03      | sK3 != X0 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_395,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.33/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.33/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | ~ r2_hidden(X0,X2)
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.33/1.03      | ~ v3_orders_2(sK3)
% 2.33/1.03      | ~ v4_orders_2(sK3)
% 2.33/1.03      | ~ l1_orders_2(sK3)
% 2.33/1.03      | v2_struct_0(sK3) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_394]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_399,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.33/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.33/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | ~ r2_hidden(X0,X2)
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_395,c_25,c_24,c_23,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1139,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.33/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.33/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,X2) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1237,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.33/1.03      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.33/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,X2) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1139,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_10,plain,
% 2.33/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.33/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/1.03      | ~ l1_orders_2(X0) ),
% 2.33/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_603,plain,
% 2.33/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.33/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/1.03      | sK3 != X0 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_604,plain,
% 2.33/1.03      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_603]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1131,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.33/1.03      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1162,plain,
% 2.33/1.03      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.33/1.03      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1131,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1685,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 2.33/1.03      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1237,c_1162]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_2000,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 2.33/1.03      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.33/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1685,c_1203]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_2657,plain,
% 2.33/1.03      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_2648,c_2000]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_6,plain,
% 2.33/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.33/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1140,plain,
% 2.33/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_5,plain,
% 2.33/1.03      ( k2_subset_1(X0) = X0 ),
% 2.33/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1155,plain,
% 2.33/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1140,c_5]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_12,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ v5_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1)
% 2.33/1.03      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 2.33/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_535,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1)
% 2.33/1.03      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 2.33/1.03      | sK3 != X1 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_536,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | ~ v3_orders_2(sK3)
% 2.33/1.03      | ~ v4_orders_2(sK3)
% 2.33/1.03      | ~ l1_orders_2(sK3)
% 2.33/1.03      | v2_struct_0(sK3)
% 2.33/1.03      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_535]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_540,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_536,c_25,c_24,c_23,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1133,plain,
% 2.33/1.03      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.33/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1167,plain,
% 2.33/1.03      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.33/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1133,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1554,plain,
% 2.33/1.03      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1155,c_1167]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_2660,plain,
% 2.33/1.03      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_2657,c_1554]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_20,negated_conjecture,
% 2.33/1.03      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.33/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_0,plain,
% 2.33/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.33/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1302,plain,
% 2.33/1.03      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 2.33/1.03      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1303,plain,
% 2.33/1.03      ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1145,plain,
% 2.33/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_18,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ v5_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1)
% 2.33/1.03      | sK2(X2,X1,X0) = X2 ),
% 2.33/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_466,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/1.03      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 2.33/1.03      | ~ v3_orders_2(X1)
% 2.33/1.03      | ~ v4_orders_2(X1)
% 2.33/1.03      | ~ l1_orders_2(X1)
% 2.33/1.03      | v2_struct_0(X1)
% 2.33/1.03      | sK2(X2,X1,X0) = X2
% 2.33/1.03      | sK3 != X1 ),
% 2.33/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_467,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 2.33/1.03      | ~ v3_orders_2(sK3)
% 2.33/1.03      | ~ v4_orders_2(sK3)
% 2.33/1.03      | ~ l1_orders_2(sK3)
% 2.33/1.03      | v2_struct_0(sK3)
% 2.33/1.03      | sK2(X1,sK3,X0) = X1 ),
% 2.33/1.03      inference(unflattening,[status(thm)],[c_466]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_471,plain,
% 2.33/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.33/1.03      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 2.33/1.03      | sK2(X1,sK3,X0) = X1 ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_467,c_25,c_24,c_23,c_21]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1136,plain,
% 2.33/1.03      ( sK2(X0,sK3,X1) = X0
% 2.33/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 2.33/1.03      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1196,plain,
% 2.33/1.03      ( sK2(X0,sK3,X1) = X0
% 2.33/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_1136,c_599]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1889,plain,
% 2.33/1.03      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1554,c_1196]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1897,plain,
% 2.33/1.03      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.33/1.03      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1889,c_1155]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1901,plain,
% 2.33/1.03      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 2.33/1.03      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1145,c_1897]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3035,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1901,c_2648]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3077,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_3035,c_1554]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3037,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(superposition,[status(thm)],[c_1901,c_2000]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3068,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.33/1.03      inference(light_normalisation,[status(thm)],[c_3037,c_1554]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3082,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.33/1.03      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.33/1.03      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(backward_subsumption_resolution,[status(thm)],[c_3077,c_3068]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_838,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1446,plain,
% 2.33/1.03      ( k1_orders_2(X0,X1) != X2
% 2.33/1.03      | k1_xboole_0 != X2
% 2.33/1.03      | k1_xboole_0 = k1_orders_2(X0,X1) ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_838]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_1929,plain,
% 2.33/1.03      ( k1_orders_2(X0,k2_struct_0(sK3)) != X1
% 2.33/1.03      | k1_xboole_0 != X1
% 2.33/1.03      | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(sK3)) ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_1446]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3351,plain,
% 2.33/1.03      ( k1_orders_2(X0,k2_struct_0(sK3)) != k1_xboole_0
% 2.33/1.03      | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(sK3))
% 2.33/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_1929]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3353,plain,
% 2.33/1.03      ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 2.33/1.03      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 2.33/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_3351]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_837,plain,( X0 = X0 ),theory(equality) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3352,plain,
% 2.33/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 2.33/1.03      inference(instantiation,[status(thm)],[c_837]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3587,plain,
% 2.33/1.03      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.33/1.03      inference(global_propositional_subsumption,
% 2.33/1.03                [status(thm)],
% 2.33/1.03                [c_2660,c_20,c_1303,c_3082,c_3353,c_3352]) ).
% 2.33/1.03  
% 2.33/1.03  cnf(c_3592,plain,
% 2.33/1.03      ( $false ),
% 2.33/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3587,c_1155]) ).
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.03  
% 2.33/1.03  ------                               Statistics
% 2.33/1.03  
% 2.33/1.03  ------ General
% 2.33/1.03  
% 2.33/1.03  abstr_ref_over_cycles:                  0
% 2.33/1.03  abstr_ref_under_cycles:                 0
% 2.33/1.03  gc_basic_clause_elim:                   0
% 2.33/1.03  forced_gc_time:                         0
% 2.33/1.03  parsing_time:                           0.029
% 2.33/1.03  unif_index_cands_time:                  0.
% 2.33/1.03  unif_index_add_time:                    0.
% 2.33/1.03  orderings_time:                         0.
% 2.33/1.03  out_proof_time:                         0.013
% 2.33/1.03  total_time:                             0.211
% 2.33/1.03  num_of_symbols:                         53
% 2.33/1.03  num_of_terms:                           2936
% 2.33/1.03  
% 2.33/1.03  ------ Preprocessing
% 2.33/1.03  
% 2.33/1.03  num_of_splits:                          0
% 2.33/1.03  num_of_split_atoms:                     0
% 2.33/1.03  num_of_reused_defs:                     0
% 2.33/1.03  num_eq_ax_congr_red:                    30
% 2.33/1.03  num_of_sem_filtered_clauses:            1
% 2.33/1.03  num_of_subtypes:                        0
% 2.33/1.03  monotx_restored_types:                  0
% 2.33/1.03  sat_num_of_epr_types:                   0
% 2.33/1.03  sat_num_of_non_cyclic_types:            0
% 2.33/1.03  sat_guarded_non_collapsed_types:        0
% 2.33/1.03  num_pure_diseq_elim:                    0
% 2.33/1.03  simp_replaced_by:                       0
% 2.33/1.03  res_preprocessed:                       107
% 2.33/1.03  prep_upred:                             0
% 2.33/1.03  prep_unflattend:                        24
% 2.33/1.03  smt_new_axioms:                         0
% 2.33/1.03  pred_elim_cands:                        4
% 2.33/1.03  pred_elim:                              7
% 2.33/1.03  pred_elim_cl:                           8
% 2.33/1.03  pred_elim_cycles:                       10
% 2.33/1.03  merged_defs:                            0
% 2.33/1.03  merged_defs_ncl:                        0
% 2.33/1.03  bin_hyper_res:                          0
% 2.33/1.03  prep_cycles:                            4
% 2.33/1.03  pred_elim_time:                         0.016
% 2.33/1.03  splitting_time:                         0.
% 2.33/1.03  sem_filter_time:                        0.
% 2.33/1.03  monotx_time:                            0.001
% 2.33/1.03  subtype_inf_time:                       0.
% 2.33/1.03  
% 2.33/1.03  ------ Problem properties
% 2.33/1.03  
% 2.33/1.03  clauses:                                18
% 2.33/1.03  conjectures:                            1
% 2.33/1.03  epr:                                    4
% 2.33/1.03  horn:                                   13
% 2.33/1.03  ground:                                 3
% 2.33/1.03  unary:                                  5
% 2.33/1.03  binary:                                 3
% 2.33/1.03  lits:                                   46
% 2.33/1.03  lits_eq:                                6
% 2.33/1.03  fd_pure:                                0
% 2.33/1.03  fd_pseudo:                              0
% 2.33/1.03  fd_cond:                                1
% 2.33/1.03  fd_pseudo_cond:                         0
% 2.33/1.03  ac_symbols:                             0
% 2.33/1.03  
% 2.33/1.03  ------ Propositional Solver
% 2.33/1.03  
% 2.33/1.03  prop_solver_calls:                      29
% 2.33/1.03  prop_fast_solver_calls:                 935
% 2.33/1.03  smt_solver_calls:                       0
% 2.33/1.03  smt_fast_solver_calls:                  0
% 2.33/1.03  prop_num_of_clauses:                    1194
% 2.33/1.03  prop_preprocess_simplified:             3955
% 2.33/1.03  prop_fo_subsumed:                       37
% 2.33/1.03  prop_solver_time:                       0.
% 2.33/1.03  smt_solver_time:                        0.
% 2.33/1.03  smt_fast_solver_time:                   0.
% 2.33/1.03  prop_fast_solver_time:                  0.
% 2.33/1.03  prop_unsat_core_time:                   0.
% 2.33/1.03  
% 2.33/1.03  ------ QBF
% 2.33/1.03  
% 2.33/1.03  qbf_q_res:                              0
% 2.33/1.03  qbf_num_tautologies:                    0
% 2.33/1.03  qbf_prep_cycles:                        0
% 2.33/1.03  
% 2.33/1.03  ------ BMC1
% 2.33/1.03  
% 2.33/1.03  bmc1_current_bound:                     -1
% 2.33/1.03  bmc1_last_solved_bound:                 -1
% 2.33/1.03  bmc1_unsat_core_size:                   -1
% 2.33/1.03  bmc1_unsat_core_parents_size:           -1
% 2.33/1.03  bmc1_merge_next_fun:                    0
% 2.33/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.03  
% 2.33/1.03  ------ Instantiation
% 2.33/1.03  
% 2.33/1.03  inst_num_of_clauses:                    354
% 2.33/1.03  inst_num_in_passive:                    74
% 2.33/1.03  inst_num_in_active:                     189
% 2.33/1.03  inst_num_in_unprocessed:                91
% 2.33/1.03  inst_num_of_loops:                      220
% 2.33/1.03  inst_num_of_learning_restarts:          0
% 2.33/1.03  inst_num_moves_active_passive:          27
% 2.33/1.03  inst_lit_activity:                      0
% 2.33/1.03  inst_lit_activity_moves:                0
% 2.33/1.03  inst_num_tautologies:                   0
% 2.33/1.03  inst_num_prop_implied:                  0
% 2.33/1.03  inst_num_existing_simplified:           0
% 2.33/1.03  inst_num_eq_res_simplified:             0
% 2.33/1.03  inst_num_child_elim:                    0
% 2.33/1.03  inst_num_of_dismatching_blockings:      88
% 2.33/1.03  inst_num_of_non_proper_insts:           336
% 2.33/1.03  inst_num_of_duplicates:                 0
% 2.33/1.03  inst_inst_num_from_inst_to_res:         0
% 2.33/1.03  inst_dismatching_checking_time:         0.
% 2.33/1.03  
% 2.33/1.03  ------ Resolution
% 2.33/1.03  
% 2.33/1.03  res_num_of_clauses:                     0
% 2.33/1.03  res_num_in_passive:                     0
% 2.33/1.03  res_num_in_active:                      0
% 2.33/1.03  res_num_of_loops:                       111
% 2.33/1.03  res_forward_subset_subsumed:            69
% 2.33/1.03  res_backward_subset_subsumed:           0
% 2.33/1.03  res_forward_subsumed:                   0
% 2.33/1.03  res_backward_subsumed:                  0
% 2.33/1.03  res_forward_subsumption_resolution:     3
% 2.33/1.03  res_backward_subsumption_resolution:    0
% 2.33/1.03  res_clause_to_clause_subsumption:       211
% 2.33/1.03  res_orphan_elimination:                 0
% 2.33/1.03  res_tautology_del:                      48
% 2.33/1.03  res_num_eq_res_simplified:              0
% 2.33/1.03  res_num_sel_changes:                    0
% 2.33/1.03  res_moves_from_active_to_pass:          0
% 2.33/1.03  
% 2.33/1.03  ------ Superposition
% 2.33/1.03  
% 2.33/1.03  sup_time_total:                         0.
% 2.33/1.03  sup_time_generating:                    0.
% 2.33/1.03  sup_time_sim_full:                      0.
% 2.33/1.03  sup_time_sim_immed:                     0.
% 2.33/1.03  
% 2.33/1.03  sup_num_of_clauses:                     63
% 2.33/1.03  sup_num_in_active:                      42
% 2.33/1.03  sup_num_in_passive:                     21
% 2.33/1.03  sup_num_of_loops:                       42
% 2.33/1.03  sup_fw_superposition:                   28
% 2.33/1.03  sup_bw_superposition:                   41
% 2.33/1.03  sup_immediate_simplified:               30
% 2.33/1.03  sup_given_eliminated:                   0
% 2.33/1.03  comparisons_done:                       0
% 2.33/1.03  comparisons_avoided:                    15
% 2.33/1.03  
% 2.33/1.03  ------ Simplifications
% 2.33/1.03  
% 2.33/1.03  
% 2.33/1.03  sim_fw_subset_subsumed:                 10
% 2.33/1.03  sim_bw_subset_subsumed:                 2
% 2.33/1.03  sim_fw_subsumed:                        2
% 2.33/1.03  sim_bw_subsumed:                        2
% 2.33/1.03  sim_fw_subsumption_res:                 4
% 2.33/1.03  sim_bw_subsumption_res:                 1
% 2.33/1.03  sim_tautology_del:                      6
% 2.33/1.03  sim_eq_tautology_del:                   0
% 2.33/1.03  sim_eq_res_simp:                        0
% 2.33/1.03  sim_fw_demodulated:                     2
% 2.33/1.03  sim_bw_demodulated:                     0
% 2.33/1.03  sim_light_normalised:                   26
% 2.33/1.03  sim_joinable_taut:                      0
% 2.33/1.03  sim_joinable_simp:                      0
% 2.33/1.03  sim_ac_normalised:                      0
% 2.33/1.03  sim_smt_subsumption:                    0
% 2.33/1.03  
%------------------------------------------------------------------------------
