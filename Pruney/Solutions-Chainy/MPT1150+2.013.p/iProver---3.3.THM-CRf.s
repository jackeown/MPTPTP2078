%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:07 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  165 (1024 expanded)
%              Number of clauses        :   98 ( 360 expanded)
%              Number of leaves         :   21 ( 208 expanded)
%              Depth                    :   24
%              Number of atoms          :  661 (4619 expanded)
%              Number of equality atoms :  289 (1164 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,
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

fof(f45,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f44])).

fof(f72,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_744,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_742,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1682,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_739])).

cnf(c_2218,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_1682])).

cnf(c_2283,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_8,c_5])).

cnf(c_2506,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0)
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2283,c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4948,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2506,c_0])).

cnf(c_4949,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4948])).

cnf(c_10455,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2218,c_4949])).

cnf(c_10456,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10455])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_741,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
    | r2_hidden(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_741])).

cnf(c_19,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_728,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_740,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_958,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_728,c_740])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_725,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_732,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1381,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_732])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_738,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1504,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1381,c_738])).

cnf(c_1546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_726])).

cnf(c_1547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1546,c_1504])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1552,plain,
    ( r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1547,c_28,c_29,c_30,c_31,c_32])).

cnf(c_1553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1552])).

cnf(c_11,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_736,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2432,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_736])).

cnf(c_2582,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2432,c_32])).

cnf(c_2583,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2582])).

cnf(c_2590,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_2583])).

cnf(c_6005,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_2590])).

cnf(c_6015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6005,c_1504])).

cnf(c_6685,plain,
    ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6015,c_28,c_29,c_30,c_31,c_32])).

cnf(c_6686,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6685])).

cnf(c_11650,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_6686])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_743,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_743,c_3])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_734,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3648,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_734])).

cnf(c_4044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3648,c_28,c_29,c_30,c_31,c_32])).

cnf(c_4045,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4044])).

cnf(c_4053,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_765,c_4045])).

cnf(c_11660,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11650,c_1504,c_4053])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_244,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1077,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_1192,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_243,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1193,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_2164,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_741])).

cnf(c_6694,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2164,c_6686])).

cnf(c_6695,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6694,c_4053])).

cnf(c_2215,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_1682])).

cnf(c_1194,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_2390,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_2508,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X0)
    | ~ v1_xboole_0(X1)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2283,c_2])).

cnf(c_5723,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2508,c_0])).

cnf(c_5724,plain,
    ( X0 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5723])).

cnf(c_9868,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2215,c_1193,c_2390,c_5724])).

cnf(c_9869,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9868])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_733])).

cnf(c_3795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3704,c_1504])).

cnf(c_4296,plain,
    ( m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3795,c_28,c_29,c_30,c_31,c_32])).

cnf(c_4297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4296])).

cnf(c_4306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4297,c_739])).

cnf(c_5350,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_765,c_4306])).

cnf(c_9882,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9869,c_5350])).

cnf(c_12422,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11660,c_22,c_1192,c_1193,c_6695,c_9882])).

cnf(c_12430,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12422,c_765])).

cnf(c_12440,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10456,c_12430])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12440,c_1193,c_1192,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.99  
% 3.87/0.99  ------  iProver source info
% 3.87/0.99  
% 3.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.99  git: non_committed_changes: false
% 3.87/0.99  git: last_make_outside_of_git: false
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  ------ Parsing...
% 3.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.99  
% 3.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.99  ------ Proving...
% 3.87/0.99  ------ Problem Properties 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  clauses                                 28
% 3.87/0.99  conjectures                             6
% 3.87/0.99  EPR                                     8
% 3.87/0.99  Horn                                    17
% 3.87/0.99  unary                                   10
% 3.87/0.99  binary                                  2
% 3.87/0.99  lits                                    110
% 3.87/0.99  lits eq                                 8
% 3.87/0.99  fd_pure                                 0
% 3.87/0.99  fd_pseudo                               0
% 3.87/0.99  fd_cond                                 0
% 3.87/0.99  fd_pseudo_cond                          3
% 3.87/0.99  AC symbols                              0
% 3.87/0.99  
% 3.87/0.99  ------ Input Options Time Limit: Unbounded
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ 
% 3.87/0.99  Current options:
% 3.87/0.99  ------ 
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  ------ Proving...
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS status Theorem for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  fof(f2,axiom,(
% 3.87/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f17,plain,(
% 3.87/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.87/0.99    inference(ennf_transformation,[],[f2])).
% 3.87/0.99  
% 3.87/0.99  fof(f34,plain,(
% 3.87/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.87/0.99    inference(nnf_transformation,[],[f17])).
% 3.87/0.99  
% 3.87/0.99  fof(f35,plain,(
% 3.87/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f36,plain,(
% 3.87/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.87/0.99  
% 3.87/0.99  fof(f47,plain,(
% 3.87/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f36])).
% 3.87/0.99  
% 3.87/0.99  fof(f5,axiom,(
% 3.87/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f51,plain,(
% 3.87/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.87/0.99    inference(cnf_transformation,[],[f5])).
% 3.87/0.99  
% 3.87/0.99  fof(f8,axiom,(
% 3.87/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f22,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.87/0.99    inference(ennf_transformation,[],[f8])).
% 3.87/0.99  
% 3.87/0.99  fof(f54,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f22])).
% 3.87/0.99  
% 3.87/0.99  fof(f1,axiom,(
% 3.87/0.99    v1_xboole_0(k1_xboole_0)),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f46,plain,(
% 3.87/0.99    v1_xboole_0(k1_xboole_0)),
% 3.87/0.99    inference(cnf_transformation,[],[f1])).
% 3.87/0.99  
% 3.87/0.99  fof(f14,axiom,(
% 3.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f30,plain,(
% 3.87/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.87/0.99    inference(ennf_transformation,[],[f14])).
% 3.87/0.99  
% 3.87/0.99  fof(f31,plain,(
% 3.87/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.87/0.99    inference(flattening,[],[f30])).
% 3.87/0.99  
% 3.87/0.99  fof(f39,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.87/0.99    inference(nnf_transformation,[],[f31])).
% 3.87/0.99  
% 3.87/0.99  fof(f40,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.87/0.99    inference(rectify,[],[f39])).
% 3.87/0.99  
% 3.87/0.99  fof(f42,plain,(
% 3.87/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f41,plain,(
% 3.87/0.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f43,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).
% 3.87/0.99  
% 3.87/0.99  fof(f62,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f6,axiom,(
% 3.87/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f18,plain,(
% 3.87/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.87/0.99    inference(ennf_transformation,[],[f6])).
% 3.87/0.99  
% 3.87/0.99  fof(f19,plain,(
% 3.87/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.87/0.99    inference(flattening,[],[f18])).
% 3.87/0.99  
% 3.87/0.99  fof(f52,plain,(
% 3.87/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f19])).
% 3.87/0.99  
% 3.87/0.99  fof(f64,plain,(
% 3.87/0.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f43])).
% 3.87/0.99  
% 3.87/0.99  fof(f7,axiom,(
% 3.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f20,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.87/0.99    inference(ennf_transformation,[],[f7])).
% 3.87/0.99  
% 3.87/0.99  fof(f21,plain,(
% 3.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.87/0.99    inference(flattening,[],[f20])).
% 3.87/0.99  
% 3.87/0.99  fof(f53,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f21])).
% 3.87/0.99  
% 3.87/0.99  fof(f15,conjecture,(
% 3.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f16,negated_conjecture,(
% 3.87/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.87/0.99    inference(negated_conjecture,[],[f15])).
% 3.87/0.99  
% 3.87/0.99  fof(f32,plain,(
% 3.87/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f16])).
% 3.87/0.99  
% 3.87/0.99  fof(f33,plain,(
% 3.87/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f32])).
% 3.87/0.99  
% 3.87/0.99  fof(f44,plain,(
% 3.87/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.87/0.99    introduced(choice_axiom,[])).
% 3.87/0.99  
% 3.87/0.99  fof(f45,plain,(
% 3.87/0.99    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f44])).
% 3.87/0.99  
% 3.87/0.99  fof(f72,plain,(
% 3.87/0.99    l1_orders_2(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f13,axiom,(
% 3.87/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f29,plain,(
% 3.87/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f13])).
% 3.87/0.99  
% 3.87/0.99  fof(f61,plain,(
% 3.87/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f29])).
% 3.87/0.99  
% 3.87/0.99  fof(f9,axiom,(
% 3.87/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f23,plain,(
% 3.87/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f9])).
% 3.87/0.99  
% 3.87/0.99  fof(f55,plain,(
% 3.87/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f23])).
% 3.87/0.99  
% 3.87/0.99  fof(f68,plain,(
% 3.87/0.99    ~v2_struct_0(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f69,plain,(
% 3.87/0.99    v3_orders_2(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f70,plain,(
% 3.87/0.99    v4_orders_2(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f71,plain,(
% 3.87/0.99    v5_orders_2(sK3)),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f10,axiom,(
% 3.87/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f24,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.87/0.99    inference(ennf_transformation,[],[f10])).
% 3.87/0.99  
% 3.87/0.99  fof(f37,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.87/0.99    inference(nnf_transformation,[],[f24])).
% 3.87/0.99  
% 3.87/0.99  fof(f38,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.87/0.99    inference(flattening,[],[f37])).
% 3.87/0.99  
% 3.87/0.99  fof(f57,plain,(
% 3.87/0.99    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f38])).
% 3.87/0.99  
% 3.87/0.99  fof(f74,plain,(
% 3.87/0.99    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.87/0.99    inference(equality_resolution,[],[f57])).
% 3.87/0.99  
% 3.87/0.99  fof(f4,axiom,(
% 3.87/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f50,plain,(
% 3.87/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.87/0.99    inference(cnf_transformation,[],[f4])).
% 3.87/0.99  
% 3.87/0.99  fof(f3,axiom,(
% 3.87/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f49,plain,(
% 3.87/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.87/0.99    inference(cnf_transformation,[],[f3])).
% 3.87/0.99  
% 3.87/0.99  fof(f11,axiom,(
% 3.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f25,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f11])).
% 3.87/0.99  
% 3.87/0.99  fof(f26,plain,(
% 3.87/0.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f25])).
% 3.87/0.99  
% 3.87/0.99  fof(f59,plain,(
% 3.87/0.99    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f26])).
% 3.87/0.99  
% 3.87/0.99  fof(f73,plain,(
% 3.87/0.99    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 3.87/0.99    inference(cnf_transformation,[],[f45])).
% 3.87/0.99  
% 3.87/0.99  fof(f12,axiom,(
% 3.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.99  
% 3.87/0.99  fof(f27,plain,(
% 3.87/0.99    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.87/0.99    inference(ennf_transformation,[],[f12])).
% 3.87/0.99  
% 3.87/0.99  fof(f28,plain,(
% 3.87/0.99    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.87/0.99    inference(flattening,[],[f27])).
% 3.87/0.99  
% 3.87/0.99  fof(f60,plain,(
% 3.87/0.99    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.87/0.99    inference(cnf_transformation,[],[f28])).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2,plain,
% 3.87/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_744,plain,
% 3.87/0.99      ( X0 = X1
% 3.87/0.99      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.87/0.99      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5,plain,
% 3.87/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_742,plain,
% 3.87/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ r2_hidden(X2,X0)
% 3.87/0.99      | ~ v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_739,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.87/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1682,plain,
% 3.87/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_742,c_739]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2218,plain,
% 3.87/0.99      ( k1_xboole_0 = X0
% 3.87/0.99      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_744,c_1682]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2283,plain,
% 3.87/0.99      ( ~ r2_hidden(X0,k1_xboole_0) | ~ v1_xboole_0(X1) ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_8,c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2506,plain,
% 3.87/0.99      ( r2_hidden(sK0(X0,k1_xboole_0),X0)
% 3.87/0.99      | ~ v1_xboole_0(X1)
% 3.87/0.99      | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2283,c_2]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_0,plain,
% 3.87/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4948,plain,
% 3.87/0.99      ( r2_hidden(sK0(X0,k1_xboole_0),X0) | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2506,c_0]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4949,plain,
% 3.87/0.99      ( k1_xboole_0 = X0
% 3.87/0.99      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4948]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10455,plain,
% 3.87/0.99      ( r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top
% 3.87/0.99      | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2218,c_4949]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_10456,plain,
% 3.87/0.99      ( k1_xboole_0 = X0
% 3.87/0.99      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_10455]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_21,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.87/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.87/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ v3_orders_2(X1)
% 3.87/0.99      | ~ v4_orders_2(X1)
% 3.87/0.99      | ~ v5_orders_2(X1)
% 3.87/0.99      | ~ l1_orders_2(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_726,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.87/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 3.87/0.99      | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(X1) = iProver_top
% 3.87/0.99      | v3_orders_2(X1) != iProver_top
% 3.87/0.99      | v4_orders_2(X1) != iProver_top
% 3.87/0.99      | v5_orders_2(X1) != iProver_top
% 3.87/0.99      | l1_orders_2(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_741,plain,
% 3.87/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.87/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.87/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2162,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.87/0.99      | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
% 3.87/0.99      | r2_hidden(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 3.87/0.99      | v2_struct_0(X1) = iProver_top
% 3.87/0.99      | v3_orders_2(X1) != iProver_top
% 3.87/0.99      | v4_orders_2(X1) != iProver_top
% 3.87/0.99      | v5_orders_2(X1) != iProver_top
% 3.87/0.99      | l1_orders_2(X1) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_726,c_741]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_19,plain,
% 3.87/0.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 3.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.87/0.99      | ~ r2_hidden(X1,X3)
% 3.87/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 3.87/0.99      | v2_struct_0(X0)
% 3.87/0.99      | ~ v3_orders_2(X0)
% 3.87/0.99      | ~ v4_orders_2(X0)
% 3.87/0.99      | ~ v5_orders_2(X0)
% 3.87/0.99      | ~ l1_orders_2(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_728,plain,
% 3.87/0.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 3.87/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,X3) != iProver_top
% 3.87/0.99      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | v3_orders_2(X0) != iProver_top
% 3.87/0.99      | v4_orders_2(X0) != iProver_top
% 3.87/0.99      | v5_orders_2(X0) != iProver_top
% 3.87/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7,plain,
% 3.87/0.99      ( m1_subset_1(X0,X1)
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ r2_hidden(X0,X2) ),
% 3.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_740,plain,
% 3.87/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.87/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_958,plain,
% 3.87/0.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 3.87/0.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,X3) != iProver_top
% 3.87/0.99      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | v3_orders_2(X0) != iProver_top
% 3.87/0.99      | v4_orders_2(X0) != iProver_top
% 3.87/0.99      | v5_orders_2(X0) != iProver_top
% 3.87/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.87/0.99      inference(forward_subsumption_resolution,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_728,c_740]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_23,negated_conjecture,
% 3.87/0.99      ( l1_orders_2(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_725,plain,
% 3.87/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_15,plain,
% 3.87/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_732,plain,
% 3.87/0.99      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1381,plain,
% 3.87/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_725,c_732]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9,plain,
% 3.87/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_738,plain,
% 3.87/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.87/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1504,plain,
% 3.87/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1381,c_738]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1546,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1504,c_726]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1547,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_1546,c_1504]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_27,negated_conjecture,
% 3.87/0.99      ( ~ v2_struct_0(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_28,plain,
% 3.87/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_26,negated_conjecture,
% 3.87/0.99      ( v3_orders_2(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_29,plain,
% 3.87/0.99      ( v3_orders_2(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_25,negated_conjecture,
% 3.87/0.99      ( v4_orders_2(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_30,plain,
% 3.87/0.99      ( v4_orders_2(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_24,negated_conjecture,
% 3.87/0.99      ( v5_orders_2(sK3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_31,plain,
% 3.87/0.99      ( v5_orders_2(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_32,plain,
% 3.87/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1552,plain,
% 3.87/0.99      ( r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_1547,c_28,c_29,c_30,c_31,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1553,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_1552]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11,plain,
% 3.87/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 3.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.87/0.99      | ~ l1_orders_2(X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_736,plain,
% 3.87/0.99      ( r2_orders_2(X0,X1,X1) != iProver_top
% 3.87/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.87/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2432,plain,
% 3.87/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1504,c_736]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2582,plain,
% 3.87/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.87/0.99      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2432,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2583,plain,
% 3.87/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_2582]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2590,plain,
% 3.87/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 3.87/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1553,c_2583]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6005,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_958,c_2590]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6015,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_6005,c_1504]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6685,plain,
% 3.87/0.99      ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_6015,c_28,c_29,c_30,c_31,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6686,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_6685]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11650,plain,
% 3.87/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,u1_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top
% 3.87/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_2162,c_6686]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4,plain,
% 3.87/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_743,plain,
% 3.87/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3,plain,
% 3.87/0.99      ( k2_subset_1(X0) = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_765,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_743,c_3]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_13,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ v3_orders_2(X1)
% 3.87/0.99      | ~ v4_orders_2(X1)
% 3.87/0.99      | ~ v5_orders_2(X1)
% 3.87/0.99      | ~ l1_orders_2(X1)
% 3.87/0.99      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_734,plain,
% 3.87/0.99      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 3.87/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.87/0.99      | v2_struct_0(X0) = iProver_top
% 3.87/0.99      | v3_orders_2(X0) != iProver_top
% 3.87/0.99      | v4_orders_2(X0) != iProver_top
% 3.87/0.99      | v5_orders_2(X0) != iProver_top
% 3.87/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3648,plain,
% 3.87/0.99      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1504,c_734]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4044,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3648,c_28,c_29,c_30,c_31,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4045,plain,
% 3.87/0.99      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_4044]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4053,plain,
% 3.87/0.99      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_765,c_4045]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_11660,plain,
% 3.87/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(light_normalisation,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_11650,c_1504,c_4053]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_22,negated_conjecture,
% 3.87/0.99      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_244,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1077,plain,
% 3.87/0.99      ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
% 3.87/0.99      | k1_xboole_0 != X0
% 3.87/0.99      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_244]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1192,plain,
% 3.87/0.99      ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 3.87/0.99      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 3.87/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1077]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_243,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1193,plain,
% 3.87/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_243]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2164,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1553,c_741]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6694,plain,
% 3.87/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_2164,c_6686]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_6695,plain,
% 3.87/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_6694,c_4053]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2215,plain,
% 3.87/0.99      ( k1_xboole_0 = X0
% 3.87/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.87/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_744,c_1682]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1194,plain,
% 3.87/0.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_244]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2390,plain,
% 3.87/0.99      ( X0 != k1_xboole_0
% 3.87/0.99      | k1_xboole_0 = X0
% 3.87/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1194]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2508,plain,
% 3.87/0.99      ( r2_hidden(sK0(k1_xboole_0,X0),X0)
% 3.87/0.99      | ~ v1_xboole_0(X1)
% 3.87/0.99      | X0 = k1_xboole_0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2283,c_2]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5723,plain,
% 3.87/0.99      ( r2_hidden(sK0(k1_xboole_0,X0),X0) | X0 = k1_xboole_0 ),
% 3.87/0.99      inference(resolution,[status(thm)],[c_2508,c_0]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5724,plain,
% 3.87/0.99      ( X0 = k1_xboole_0
% 3.87/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5723]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9868,plain,
% 3.87/0.99      ( r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 3.87/0.99      | k1_xboole_0 = X0 ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_2215,c_1193,c_2390,c_5724]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9869,plain,
% 3.87/0.99      ( k1_xboole_0 = X0
% 3.87/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_9868]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_14,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.87/0.99      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.87/0.99      | v2_struct_0(X1)
% 3.87/0.99      | ~ v3_orders_2(X1)
% 3.87/0.99      | ~ v4_orders_2(X1)
% 3.87/0.99      | ~ v5_orders_2(X1)
% 3.87/0.99      | ~ l1_orders_2(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_733,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.87/0.99      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.87/0.99      | v2_struct_0(X1) = iProver_top
% 3.87/0.99      | v3_orders_2(X1) != iProver_top
% 3.87/0.99      | v4_orders_2(X1) != iProver_top
% 3.87/0.99      | v5_orders_2(X1) != iProver_top
% 3.87/0.99      | l1_orders_2(X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3704,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1504,c_733]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3795,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.87/0.99      | v2_struct_0(sK3) = iProver_top
% 3.87/0.99      | v3_orders_2(sK3) != iProver_top
% 3.87/0.99      | v4_orders_2(sK3) != iProver_top
% 3.87/0.99      | v5_orders_2(sK3) != iProver_top
% 3.87/0.99      | l1_orders_2(sK3) != iProver_top ),
% 3.87/0.99      inference(light_normalisation,[status(thm)],[c_3704,c_1504]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4296,plain,
% 3.87/0.99      ( m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.87/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3795,c_28,c_29,c_30,c_31,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4297,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_4296]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4306,plain,
% 3.87/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4297,c_739]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5350,plain,
% 3.87/0.99      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_765,c_4306]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_9882,plain,
% 3.87/0.99      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.87/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_9869,c_5350]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12422,plain,
% 3.87/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.87/0.99      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_11660,c_22,c_1192,c_1193,c_6695,c_9882]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12430,plain,
% 3.87/0.99      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.87/0.99      inference(forward_subsumption_resolution,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_12422,c_765]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_12440,plain,
% 3.87/0.99      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_10456,c_12430]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(contradiction,plain,
% 3.87/0.99      ( $false ),
% 3.87/0.99      inference(minisat,[status(thm)],[c_12440,c_1193,c_1192,c_22]) ).
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  ------                               Statistics
% 3.87/0.99  
% 3.87/0.99  ------ Selected
% 3.87/0.99  
% 3.87/0.99  total_time:                             0.368
% 3.87/0.99  
%------------------------------------------------------------------------------
