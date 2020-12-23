%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:07 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  164 (1856 expanded)
%              Number of clauses        :  103 ( 526 expanded)
%              Number of leaves         :   18 ( 406 expanded)
%              Depth                    :   25
%              Number of atoms          :  692 (9029 expanded)
%              Number of equality atoms :  220 (1730 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
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

fof(f39,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

fof(f61,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f37])).

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
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(cnf_transformation,[],[f37])).

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

fof(f19,plain,(
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

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1096,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1096,c_1])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_23,c_22,c_21,c_19])).

cnf(c_1087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_252,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_586,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_19])).

cnf(c_587,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_1127,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1087,c_587])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_23,c_22,c_21,c_19])).

cnf(c_1086,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1116,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1086,c_587])).

cnf(c_1289,plain,
    ( a_2_0_orders_2(sK3,k1_orders_2(sK3,X0)) = k1_orders_2(sK3,k1_orders_2(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1116])).

cnf(c_2004,plain,
    ( a_2_0_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3))) = k1_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_1104,c_1289])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_23,c_22,c_21,c_19])).

cnf(c_1088,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_1152,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1088,c_587])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1094,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1714,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1094])).

cnf(c_2408,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1714])).

cnf(c_2854,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k1_orders_2(sK3,X1))) = iProver_top
    | v1_xboole_0(k1_orders_2(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_2408])).

cnf(c_2979,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
    | v1_xboole_0(k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_2854])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1241,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1242,plain,
    ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_1097,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_23,c_22,c_21,c_19])).

cnf(c_1090,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_1138,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1090,c_587])).

cnf(c_1465,plain,
    ( sK2(sK0(a_2_0_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_0_orders_2(sK3,X0))
    | a_2_0_orders_2(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_1138])).

cnf(c_2251,plain,
    ( sK2(sK0(a_2_0_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_0_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1104,c_1465])).

cnf(c_1566,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1104,c_1116])).

cnf(c_2261,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2251,c_1566])).

cnf(c_2262,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2261,c_1566])).

cnf(c_832,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6781,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_833,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1460,plain,
    ( k1_orders_2(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k1_orders_2(X0,X1) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_3095,plain,
    ( k1_orders_2(X0,k2_struct_0(X1)) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_7837,plain,
    ( k1_orders_2(X0,k2_struct_0(X1)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3095])).

cnf(c_7838,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7837])).

cnf(c_8761,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_18,c_6781,c_7838])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_23,c_22,c_21,c_19])).

cnf(c_1091,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1091,c_587])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1095,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1095])).

cnf(c_1715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1094])).

cnf(c_2093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,k1_orders_2(sK3,X0))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1715])).

cnf(c_2224,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,k1_orders_2(sK3,X1)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k1_orders_2(sK3,k1_orders_2(sK3,X1)))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_2093])).

cnf(c_2092,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1715])).

cnf(c_2853,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_2408])).

cnf(c_2866,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2853,c_1566])).

cnf(c_3756,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_2092,c_2866])).

cnf(c_3764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_3756])).

cnf(c_3776,plain,
    ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1573,c_3764])).

cnf(c_3777,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3776])).

cnf(c_8766,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8761,c_3777])).

cnf(c_8800,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8766,c_1566])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_374,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_375,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_379,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_23,c_22,c_21,c_19])).

cnf(c_1093,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1179,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1093,c_587])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_591,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_592,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1085,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1111,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1085,c_587])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1111])).

cnf(c_3063,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1739,c_1145])).

cnf(c_8767,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8761,c_3063])).

cnf(c_8793,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8767,c_1566])).

cnf(c_8804,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8800,c_8793])).

cnf(c_11067,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2979,c_18,c_1242,c_8804])).

cnf(c_11072,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11067,c_1104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:35:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.98  
% 3.37/0.98  ------  iProver source info
% 3.37/0.98  
% 3.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.98  git: non_committed_changes: false
% 3.37/0.98  git: last_make_outside_of_git: false
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     num_symb
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       true
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Simplification Setup
% 3.37/0.99  
% 3.37/0.99  --sup_indices_passive                   []
% 3.37/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_full_bw                           [BwDemod]
% 3.37/0.99  --sup_immed_triv                        [TrivRules]
% 3.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_immed_bw_main                     []
% 3.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  
% 3.37/0.99  ------ Combination Options
% 3.37/0.99  
% 3.37/0.99  --comb_res_mult                         3
% 3.37/0.99  --comb_sup_mult                         2
% 3.37/0.99  --comb_inst_mult                        10
% 3.37/0.99  
% 3.37/0.99  ------ Debug Options
% 3.37/0.99  
% 3.37/0.99  --dbg_backtrace                         false
% 3.37/0.99  --dbg_dump_prop_clauses                 false
% 3.37/0.99  --dbg_dump_prop_clauses_file            -
% 3.37/0.99  --dbg_out_stat                          false
% 3.37/0.99  ------ Parsing...
% 3.37/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.99  ------ Proving...
% 3.37/0.99  ------ Problem Properties 
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  clauses                                 16
% 3.37/0.99  conjectures                             1
% 3.37/0.99  EPR                                     1
% 3.37/0.99  Horn                                    12
% 3.37/0.99  unary                                   4
% 3.37/0.99  binary                                  4
% 3.37/0.99  lits                                    41
% 3.37/0.99  lits eq                                 6
% 3.37/0.99  fd_pure                                 0
% 3.37/0.99  fd_pseudo                               0
% 3.37/0.99  fd_cond                                 1
% 3.37/0.99  fd_pseudo_cond                          0
% 3.37/0.99  AC symbols                              0
% 3.37/0.99  
% 3.37/0.99  ------ Schedule dynamic 5 is on 
% 3.37/0.99  
% 3.37/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ 
% 3.37/0.99  Current options:
% 3.37/0.99  ------ 
% 3.37/0.99  
% 3.37/0.99  ------ Input Options
% 3.37/0.99  
% 3.37/0.99  --out_options                           all
% 3.37/0.99  --tptp_safe_out                         true
% 3.37/0.99  --problem_path                          ""
% 3.37/0.99  --include_path                          ""
% 3.37/0.99  --clausifier                            res/vclausify_rel
% 3.37/0.99  --clausifier_options                    --mode clausify
% 3.37/0.99  --stdin                                 false
% 3.37/0.99  --stats_out                             all
% 3.37/0.99  
% 3.37/0.99  ------ General Options
% 3.37/0.99  
% 3.37/0.99  --fof                                   false
% 3.37/0.99  --time_out_real                         305.
% 3.37/0.99  --time_out_virtual                      -1.
% 3.37/0.99  --symbol_type_check                     false
% 3.37/0.99  --clausify_out                          false
% 3.37/0.99  --sig_cnt_out                           false
% 3.37/0.99  --trig_cnt_out                          false
% 3.37/0.99  --trig_cnt_out_tolerance                1.
% 3.37/0.99  --trig_cnt_out_sk_spl                   false
% 3.37/0.99  --abstr_cl_out                          false
% 3.37/0.99  
% 3.37/0.99  ------ Global Options
% 3.37/0.99  
% 3.37/0.99  --schedule                              default
% 3.37/0.99  --add_important_lit                     false
% 3.37/0.99  --prop_solver_per_cl                    1000
% 3.37/0.99  --min_unsat_core                        false
% 3.37/0.99  --soft_assumptions                      false
% 3.37/0.99  --soft_lemma_size                       3
% 3.37/0.99  --prop_impl_unit_size                   0
% 3.37/0.99  --prop_impl_unit                        []
% 3.37/0.99  --share_sel_clauses                     true
% 3.37/0.99  --reset_solvers                         false
% 3.37/0.99  --bc_imp_inh                            [conj_cone]
% 3.37/0.99  --conj_cone_tolerance                   3.
% 3.37/0.99  --extra_neg_conj                        none
% 3.37/0.99  --large_theory_mode                     true
% 3.37/0.99  --prolific_symb_bound                   200
% 3.37/0.99  --lt_threshold                          2000
% 3.37/0.99  --clause_weak_htbl                      true
% 3.37/0.99  --gc_record_bc_elim                     false
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing Options
% 3.37/0.99  
% 3.37/0.99  --preprocessing_flag                    true
% 3.37/0.99  --time_out_prep_mult                    0.1
% 3.37/0.99  --splitting_mode                        input
% 3.37/0.99  --splitting_grd                         true
% 3.37/0.99  --splitting_cvd                         false
% 3.37/0.99  --splitting_cvd_svl                     false
% 3.37/0.99  --splitting_nvd                         32
% 3.37/0.99  --sub_typing                            true
% 3.37/0.99  --prep_gs_sim                           true
% 3.37/0.99  --prep_unflatten                        true
% 3.37/0.99  --prep_res_sim                          true
% 3.37/0.99  --prep_upred                            true
% 3.37/0.99  --prep_sem_filter                       exhaustive
% 3.37/0.99  --prep_sem_filter_out                   false
% 3.37/0.99  --pred_elim                             true
% 3.37/0.99  --res_sim_input                         true
% 3.37/0.99  --eq_ax_congr_red                       true
% 3.37/0.99  --pure_diseq_elim                       true
% 3.37/0.99  --brand_transform                       false
% 3.37/0.99  --non_eq_to_eq                          false
% 3.37/0.99  --prep_def_merge                        true
% 3.37/0.99  --prep_def_merge_prop_impl              false
% 3.37/0.99  --prep_def_merge_mbd                    true
% 3.37/0.99  --prep_def_merge_tr_red                 false
% 3.37/0.99  --prep_def_merge_tr_cl                  false
% 3.37/0.99  --smt_preprocessing                     true
% 3.37/0.99  --smt_ac_axioms                         fast
% 3.37/0.99  --preprocessed_out                      false
% 3.37/0.99  --preprocessed_stats                    false
% 3.37/0.99  
% 3.37/0.99  ------ Abstraction refinement Options
% 3.37/0.99  
% 3.37/0.99  --abstr_ref                             []
% 3.37/0.99  --abstr_ref_prep                        false
% 3.37/0.99  --abstr_ref_until_sat                   false
% 3.37/0.99  --abstr_ref_sig_restrict                funpre
% 3.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.99  --abstr_ref_under                       []
% 3.37/0.99  
% 3.37/0.99  ------ SAT Options
% 3.37/0.99  
% 3.37/0.99  --sat_mode                              false
% 3.37/0.99  --sat_fm_restart_options                ""
% 3.37/0.99  --sat_gr_def                            false
% 3.37/0.99  --sat_epr_types                         true
% 3.37/0.99  --sat_non_cyclic_types                  false
% 3.37/0.99  --sat_finite_models                     false
% 3.37/0.99  --sat_fm_lemmas                         false
% 3.37/0.99  --sat_fm_prep                           false
% 3.37/0.99  --sat_fm_uc_incr                        true
% 3.37/0.99  --sat_out_model                         small
% 3.37/0.99  --sat_out_clauses                       false
% 3.37/0.99  
% 3.37/0.99  ------ QBF Options
% 3.37/0.99  
% 3.37/0.99  --qbf_mode                              false
% 3.37/0.99  --qbf_elim_univ                         false
% 3.37/0.99  --qbf_dom_inst                          none
% 3.37/0.99  --qbf_dom_pre_inst                      false
% 3.37/0.99  --qbf_sk_in                             false
% 3.37/0.99  --qbf_pred_elim                         true
% 3.37/0.99  --qbf_split                             512
% 3.37/0.99  
% 3.37/0.99  ------ BMC1 Options
% 3.37/0.99  
% 3.37/0.99  --bmc1_incremental                      false
% 3.37/0.99  --bmc1_axioms                           reachable_all
% 3.37/0.99  --bmc1_min_bound                        0
% 3.37/0.99  --bmc1_max_bound                        -1
% 3.37/0.99  --bmc1_max_bound_default                -1
% 3.37/0.99  --bmc1_symbol_reachability              true
% 3.37/0.99  --bmc1_property_lemmas                  false
% 3.37/0.99  --bmc1_k_induction                      false
% 3.37/0.99  --bmc1_non_equiv_states                 false
% 3.37/0.99  --bmc1_deadlock                         false
% 3.37/0.99  --bmc1_ucm                              false
% 3.37/0.99  --bmc1_add_unsat_core                   none
% 3.37/0.99  --bmc1_unsat_core_children              false
% 3.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.99  --bmc1_out_stat                         full
% 3.37/0.99  --bmc1_ground_init                      false
% 3.37/0.99  --bmc1_pre_inst_next_state              false
% 3.37/0.99  --bmc1_pre_inst_state                   false
% 3.37/0.99  --bmc1_pre_inst_reach_state             false
% 3.37/0.99  --bmc1_out_unsat_core                   false
% 3.37/0.99  --bmc1_aig_witness_out                  false
% 3.37/0.99  --bmc1_verbose                          false
% 3.37/0.99  --bmc1_dump_clauses_tptp                false
% 3.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.99  --bmc1_dump_file                        -
% 3.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.99  --bmc1_ucm_extend_mode                  1
% 3.37/0.99  --bmc1_ucm_init_mode                    2
% 3.37/0.99  --bmc1_ucm_cone_mode                    none
% 3.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.99  --bmc1_ucm_relax_model                  4
% 3.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.99  --bmc1_ucm_layered_model                none
% 3.37/0.99  --bmc1_ucm_max_lemma_size               10
% 3.37/0.99  
% 3.37/0.99  ------ AIG Options
% 3.37/0.99  
% 3.37/0.99  --aig_mode                              false
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation Options
% 3.37/0.99  
% 3.37/0.99  --instantiation_flag                    true
% 3.37/0.99  --inst_sos_flag                         false
% 3.37/0.99  --inst_sos_phase                        true
% 3.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel_side                     none
% 3.37/0.99  --inst_solver_per_active                1400
% 3.37/0.99  --inst_solver_calls_frac                1.
% 3.37/0.99  --inst_passive_queue_type               priority_queues
% 3.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.99  --inst_passive_queues_freq              [25;2]
% 3.37/0.99  --inst_dismatching                      true
% 3.37/0.99  --inst_eager_unprocessed_to_passive     true
% 3.37/0.99  --inst_prop_sim_given                   true
% 3.37/0.99  --inst_prop_sim_new                     false
% 3.37/0.99  --inst_subs_new                         false
% 3.37/0.99  --inst_eq_res_simp                      false
% 3.37/0.99  --inst_subs_given                       false
% 3.37/0.99  --inst_orphan_elimination               true
% 3.37/0.99  --inst_learning_loop_flag               true
% 3.37/0.99  --inst_learning_start                   3000
% 3.37/0.99  --inst_learning_factor                  2
% 3.37/0.99  --inst_start_prop_sim_after_learn       3
% 3.37/0.99  --inst_sel_renew                        solver
% 3.37/0.99  --inst_lit_activity_flag                true
% 3.37/0.99  --inst_restr_to_given                   false
% 3.37/0.99  --inst_activity_threshold               500
% 3.37/0.99  --inst_out_proof                        true
% 3.37/0.99  
% 3.37/0.99  ------ Resolution Options
% 3.37/0.99  
% 3.37/0.99  --resolution_flag                       false
% 3.37/0.99  --res_lit_sel                           adaptive
% 3.37/0.99  --res_lit_sel_side                      none
% 3.37/0.99  --res_ordering                          kbo
% 3.37/0.99  --res_to_prop_solver                    active
% 3.37/0.99  --res_prop_simpl_new                    false
% 3.37/0.99  --res_prop_simpl_given                  true
% 3.37/0.99  --res_passive_queue_type                priority_queues
% 3.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.99  --res_passive_queues_freq               [15;5]
% 3.37/0.99  --res_forward_subs                      full
% 3.37/0.99  --res_backward_subs                     full
% 3.37/0.99  --res_forward_subs_resolution           true
% 3.37/0.99  --res_backward_subs_resolution          true
% 3.37/0.99  --res_orphan_elimination                true
% 3.37/0.99  --res_time_limit                        2.
% 3.37/0.99  --res_out_proof                         true
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Options
% 3.37/0.99  
% 3.37/0.99  --superposition_flag                    true
% 3.37/0.99  --sup_passive_queue_type                priority_queues
% 3.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.99  --demod_completeness_check              fast
% 3.37/0.99  --demod_use_ground                      true
% 3.37/0.99  --sup_to_prop_solver                    passive
% 3.37/0.99  --sup_prop_simpl_new                    true
% 3.37/0.99  --sup_prop_simpl_given                  true
% 3.37/0.99  --sup_fun_splitting                     false
% 3.37/0.99  --sup_smt_interval                      50000
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Simplification Setup
% 3.37/0.99  
% 3.37/0.99  --sup_indices_passive                   []
% 3.37/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_full_bw                           [BwDemod]
% 3.37/0.99  --sup_immed_triv                        [TrivRules]
% 3.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_immed_bw_main                     []
% 3.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.99  
% 3.37/0.99  ------ Combination Options
% 3.37/0.99  
% 3.37/0.99  --comb_res_mult                         3
% 3.37/0.99  --comb_sup_mult                         2
% 3.37/0.99  --comb_inst_mult                        10
% 3.37/0.99  
% 3.37/0.99  ------ Debug Options
% 3.37/0.99  
% 3.37/0.99  --dbg_backtrace                         false
% 3.37/0.99  --dbg_dump_prop_clauses                 false
% 3.37/0.99  --dbg_dump_prop_clauses_file            -
% 3.37/0.99  --dbg_out_stat                          false
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ Proving...
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS status Theorem for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99   Resolution empty clause
% 3.37/0.99  
% 3.37/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  fof(f3,axiom,(
% 3.37/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f42,plain,(
% 3.37/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.37/0.99    inference(cnf_transformation,[],[f3])).
% 3.37/0.99  
% 3.37/0.99  fof(f2,axiom,(
% 3.37/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f41,plain,(
% 3.37/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.37/0.99    inference(cnf_transformation,[],[f2])).
% 3.37/0.99  
% 3.37/0.99  fof(f9,axiom,(
% 3.37/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f22,plain,(
% 3.37/0.99    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f9])).
% 3.37/0.99  
% 3.37/0.99  fof(f23,plain,(
% 3.37/0.99    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f22])).
% 3.37/0.99  
% 3.37/0.99  fof(f50,plain,(
% 3.37/0.99    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f12,conjecture,(
% 3.37/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f13,negated_conjecture,(
% 3.37/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.37/0.99    inference(negated_conjecture,[],[f12])).
% 3.37/0.99  
% 3.37/0.99  fof(f27,plain,(
% 3.37/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f13])).
% 3.37/0.99  
% 3.37/0.99  fof(f28,plain,(
% 3.37/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f27])).
% 3.37/0.99  
% 3.37/0.99  fof(f38,plain,(
% 3.37/0.99    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f39,plain,(
% 3.37/0.99    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 3.37/0.99  
% 3.37/0.99  fof(f61,plain,(
% 3.37/0.99    v5_orders_2(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f58,plain,(
% 3.37/0.99    ~v2_struct_0(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f59,plain,(
% 3.37/0.99    v3_orders_2(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f60,plain,(
% 3.37/0.99    v4_orders_2(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f62,plain,(
% 3.37/0.99    l1_orders_2(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f10,axiom,(
% 3.37/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f24,plain,(
% 3.37/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f10])).
% 3.37/0.99  
% 3.37/0.99  fof(f51,plain,(
% 3.37/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f24])).
% 3.37/0.99  
% 3.37/0.99  fof(f6,axiom,(
% 3.37/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f18,plain,(
% 3.37/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f6])).
% 3.37/0.99  
% 3.37/0.99  fof(f45,plain,(
% 3.37/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f18])).
% 3.37/0.99  
% 3.37/0.99  fof(f8,axiom,(
% 3.37/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f20,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f8])).
% 3.37/0.99  
% 3.37/0.99  fof(f21,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f20])).
% 3.37/0.99  
% 3.37/0.99  fof(f49,plain,(
% 3.37/0.99    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f21])).
% 3.37/0.99  
% 3.37/0.99  fof(f11,axiom,(
% 3.37/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f25,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.37/0.99    inference(ennf_transformation,[],[f11])).
% 3.37/0.99  
% 3.37/0.99  fof(f26,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.37/0.99    inference(flattening,[],[f25])).
% 3.37/0.99  
% 3.37/0.99  fof(f33,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.37/0.99    inference(nnf_transformation,[],[f26])).
% 3.37/0.99  
% 3.37/0.99  fof(f34,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.37/0.99    inference(rectify,[],[f33])).
% 3.37/0.99  
% 3.37/0.99  fof(f36,plain,(
% 3.37/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f35,plain,(
% 3.37/0.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f37,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 3.37/0.99  
% 3.37/0.99  fof(f56,plain,(
% 3.37/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f37])).
% 3.37/0.99  
% 3.37/0.99  fof(f66,plain,(
% 3.37/0.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.37/0.99    inference(equality_resolution,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f5,axiom,(
% 3.37/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f17,plain,(
% 3.37/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.37/0.99    inference(ennf_transformation,[],[f5])).
% 3.37/0.99  
% 3.37/0.99  fof(f44,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f17])).
% 3.37/0.99  
% 3.37/0.99  fof(f63,plain,(
% 3.37/0.99    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 3.37/0.99    inference(cnf_transformation,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f1,axiom,(
% 3.37/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f14,plain,(
% 3.37/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.37/0.99    inference(ennf_transformation,[],[f1])).
% 3.37/0.99  
% 3.37/0.99  fof(f29,plain,(
% 3.37/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f30,plain,(
% 3.37/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).
% 3.37/0.99  
% 3.37/0.99  fof(f40,plain,(
% 3.37/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.37/0.99    inference(cnf_transformation,[],[f30])).
% 3.37/0.99  
% 3.37/0.99  fof(f53,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f37])).
% 3.37/0.99  
% 3.37/0.99  fof(f52,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f37])).
% 3.37/0.99  
% 3.37/0.99  fof(f4,axiom,(
% 3.37/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f15,plain,(
% 3.37/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.37/0.99    inference(ennf_transformation,[],[f4])).
% 3.37/0.99  
% 3.37/0.99  fof(f16,plain,(
% 3.37/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.37/0.99    inference(flattening,[],[f15])).
% 3.37/0.99  
% 3.37/0.99  fof(f43,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f16])).
% 3.37/0.99  
% 3.37/0.99  fof(f54,plain,(
% 3.37/0.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f37])).
% 3.37/0.99  
% 3.37/0.99  fof(f7,axiom,(
% 3.37/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.37/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f19,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f7])).
% 3.37/0.99  
% 3.37/0.99  fof(f31,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f19])).
% 3.37/0.99  
% 3.37/0.99  fof(f32,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.37/0.99    inference(flattening,[],[f31])).
% 3.37/0.99  
% 3.37/0.99  fof(f47,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f32])).
% 3.37/0.99  
% 3.37/0.99  fof(f64,plain,(
% 3.37/0.99    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.37/0.99    inference(equality_resolution,[],[f47])).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2,plain,
% 3.37/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1096,plain,
% 3.37/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1,plain,
% 3.37/0.99      ( k2_subset_1(X0) = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1104,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1096,c_1]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ v5_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_20,negated_conjecture,
% 3.37/0.99      ( v5_orders_2(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_515,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | sK3 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_516,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_23,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_22,negated_conjecture,
% 3.37/0.99      ( v3_orders_2(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_21,negated_conjecture,
% 3.37/0.99      ( v4_orders_2(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_19,negated_conjecture,
% 3.37/0.99      ( l1_orders_2(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_520,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_516,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1087,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11,plain,
% 3.37/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5,plain,
% 3.37/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_252,plain,
% 3.37/0.99      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.37/0.99      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_586,plain,
% 3.37/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_252,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_587,plain,
% 3.37/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_586]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1127,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1087,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ v5_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_533,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 3.37/0.99      | sK3 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_534,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3)
% 3.37/0.99      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_538,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_534,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1086,plain,
% 3.37/0.99      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1116,plain,
% 3.37/0.99      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1086,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1289,plain,
% 3.37/0.99      ( a_2_0_orders_2(sK3,k1_orders_2(sK3,X0)) = k1_orders_2(sK3,k1_orders_2(sK3,X0))
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1127,c_1116]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2004,plain,
% 3.37/0.99      ( a_2_0_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3))) = k1_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_1289]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_13,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 3.37/0.99      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ v5_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_491,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 3.37/0.99      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | sK3 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_492,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.37/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 3.37/0.99      | r2_hidden(sK1(sK3,X1,X0),X1)
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_496,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.37/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 3.37/0.99      | r2_hidden(sK1(sK3,X1,X0),X1) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_492,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1088,plain,
% 3.37/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 3.37/0.99      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1152,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 3.37/0.99      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1088,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.37/0.99      | ~ r2_hidden(X2,X0)
% 3.37/0.99      | ~ v1_xboole_0(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1094,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.37/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.37/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1714,plain,
% 3.37/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_1094]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2408,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 3.37/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1152,c_1714]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2854,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k1_orders_2(sK3,X1))) = iProver_top
% 3.37/0.99      | v1_xboole_0(k1_orders_2(sK3,X1)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1127,c_2408]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2979,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,k1_orders_2(sK3,k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
% 3.37/0.99      | v1_xboole_0(k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_2004,c_2854]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_18,negated_conjecture,
% 3.37/0.99      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_0,plain,
% 3.37/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1241,plain,
% 3.37/0.99      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 3.37/0.99      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1242,plain,
% 3.37/0.99      ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1097,plain,
% 3.37/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_16,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ v5_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | sK2(X2,X1,X0) = X2 ),
% 3.37/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_446,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | sK2(X2,X1,X0) = X2
% 3.37/0.99      | sK3 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_447,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3)
% 3.37/0.99      | sK2(X1,sK3,X0) = X1 ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_451,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 3.37/0.99      | sK2(X1,sK3,X0) = X1 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_447,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1090,plain,
% 3.37/0.99      ( sK2(X0,sK3,X1) = X0
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1138,plain,
% 3.37/0.99      ( sK2(X0,sK3,X1) = X0
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1090,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1465,plain,
% 3.37/0.99      ( sK2(sK0(a_2_0_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_0_orders_2(sK3,X0))
% 3.37/0.99      | a_2_0_orders_2(sK3,X0) = k1_xboole_0
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1097,c_1138]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2251,plain,
% 3.37/0.99      ( sK2(sK0(a_2_0_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_0_orders_2(sK3,k2_struct_0(sK3)))
% 3.37/0.99      | a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_1465]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1566,plain,
% 3.37/0.99      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_1116]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2261,plain,
% 3.37/0.99      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 3.37/0.99      | a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_2251,c_1566]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2262,plain,
% 3.37/0.99      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 3.37/0.99      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.37/0.99      inference(demodulation,[status(thm)],[c_2261,c_1566]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_832,plain,( X0 = X0 ),theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6781,plain,
% 3.37/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_832]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_833,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1460,plain,
% 3.37/0.99      ( k1_orders_2(X0,X1) != X2
% 3.37/0.99      | k1_xboole_0 != X2
% 3.37/0.99      | k1_xboole_0 = k1_orders_2(X0,X1) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_833]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3095,plain,
% 3.37/0.99      ( k1_orders_2(X0,k2_struct_0(X1)) != X2
% 3.37/0.99      | k1_xboole_0 != X2
% 3.37/0.99      | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X1)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1460]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7837,plain,
% 3.37/0.99      ( k1_orders_2(X0,k2_struct_0(X1)) != k1_xboole_0
% 3.37/0.99      | k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X1))
% 3.37/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_3095]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7838,plain,
% 3.37/0.99      ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 3.37/0.99      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 3.37/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_7837]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8761,plain,
% 3.37/0.99      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2262,c_18,c_6781,c_7838]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_17,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ v5_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_425,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v3_orders_2(X1)
% 3.37/0.99      | ~ v4_orders_2(X1)
% 3.37/0.99      | ~ l1_orders_2(X1)
% 3.37/0.99      | sK3 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_426,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_430,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_426,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1091,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1145,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1091,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3,plain,
% 3.37/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1095,plain,
% 3.37/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.37/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.37/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1573,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1145,c_1095]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1715,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1127,c_1094]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2093,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,k1_orders_2(sK3,k1_orders_2(sK3,X0))) != iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1127,c_1715]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2224,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(k1_orders_2(sK3,k1_orders_2(sK3,X1)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k1_orders_2(sK3,k1_orders_2(sK3,X1)))) = iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1152,c_2093]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2092,plain,
% 3.37/0.99      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_1715]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2853,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1104,c_2408]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2866,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_2853,c_1566]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3756,plain,
% 3.37/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2224,c_2092,c_2866]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3764,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1145,c_3756]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3776,plain,
% 3.37/0.99      ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1573,c_3764]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3777,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_3776]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8766,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8761,c_3777]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8800,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_8766,c_1566]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_15,plain,
% 3.37/0.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 3.37/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/0.99      | ~ r2_hidden(X1,X3)
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v3_orders_2(X0)
% 3.37/0.99      | ~ v4_orders_2(X0)
% 3.37/0.99      | ~ v5_orders_2(X0)
% 3.37/0.99      | ~ l1_orders_2(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_374,plain,
% 3.37/0.99      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 3.37/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.37/0.99      | ~ r2_hidden(X1,X3)
% 3.37/0.99      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v3_orders_2(X0)
% 3.37/0.99      | ~ v4_orders_2(X0)
% 3.37/0.99      | ~ l1_orders_2(X0)
% 3.37/0.99      | sK3 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_375,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 3.37/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | ~ r2_hidden(X0,X2)
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 3.37/0.99      | v2_struct_0(sK3)
% 3.37/0.99      | ~ v3_orders_2(sK3)
% 3.37/0.99      | ~ v4_orders_2(sK3)
% 3.37/0.99      | ~ l1_orders_2(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_379,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 3.37/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.37/0.99      | ~ r2_hidden(X0,X2)
% 3.37/0.99      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_375,c_23,c_22,c_21,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1093,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1179,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 3.37/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1093,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7,plain,
% 3.37/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 3.37/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/0.99      | ~ l1_orders_2(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_591,plain,
% 3.37/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 3.37/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/0.99      | sK3 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_592,plain,
% 3.37/0.99      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_591]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1085,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1111,plain,
% 3.37/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.37/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1085,c_587]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1739,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1179,c_1111]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3063,plain,
% 3.37/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 3.37/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1739,c_1145]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8767,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_8761,c_3063]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8793,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_8767,c_1566]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8804,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_8800,c_8793]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11067,plain,
% 3.37/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2979,c_18,c_1242,c_8804]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11072,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11067,c_1104]) ).
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  ------                               Statistics
% 3.37/0.99  
% 3.37/0.99  ------ General
% 3.37/0.99  
% 3.37/0.99  abstr_ref_over_cycles:                  0
% 3.37/0.99  abstr_ref_under_cycles:                 0
% 3.37/0.99  gc_basic_clause_elim:                   0
% 3.37/0.99  forced_gc_time:                         0
% 3.37/0.99  parsing_time:                           0.045
% 3.37/0.99  unif_index_cands_time:                  0.
% 3.37/0.99  unif_index_add_time:                    0.
% 3.37/0.99  orderings_time:                         0.
% 3.37/0.99  out_proof_time:                         0.015
% 3.37/0.99  total_time:                             0.435
% 3.37/0.99  num_of_symbols:                         53
% 3.37/0.99  num_of_terms:                           12147
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing
% 3.37/0.99  
% 3.37/0.99  num_of_splits:                          0
% 3.37/0.99  num_of_split_atoms:                     0
% 3.37/0.99  num_of_reused_defs:                     0
% 3.37/0.99  num_eq_ax_congr_red:                    33
% 3.37/0.99  num_of_sem_filtered_clauses:            1
% 3.37/0.99  num_of_subtypes:                        0
% 3.37/0.99  monotx_restored_types:                  0
% 3.37/0.99  sat_num_of_epr_types:                   0
% 3.37/0.99  sat_num_of_non_cyclic_types:            0
% 3.37/0.99  sat_guarded_non_collapsed_types:        0
% 3.37/0.99  num_pure_diseq_elim:                    0
% 3.37/0.99  simp_replaced_by:                       0
% 3.37/0.99  res_preprocessed:                       97
% 3.37/0.99  prep_upred:                             0
% 3.37/0.99  prep_unflattend:                        24
% 3.37/0.99  smt_new_axioms:                         0
% 3.37/0.99  pred_elim_cands:                        4
% 3.37/0.99  pred_elim:                              7
% 3.37/0.99  pred_elim_cl:                           8
% 3.37/0.99  pred_elim_cycles:                       12
% 3.37/0.99  merged_defs:                            0
% 3.37/0.99  merged_defs_ncl:                        0
% 3.37/0.99  bin_hyper_res:                          0
% 3.37/0.99  prep_cycles:                            4
% 3.37/0.99  pred_elim_time:                         0.017
% 3.37/0.99  splitting_time:                         0.
% 3.37/0.99  sem_filter_time:                        0.
% 3.37/0.99  monotx_time:                            0.
% 3.37/0.99  subtype_inf_time:                       0.
% 3.37/0.99  
% 3.37/0.99  ------ Problem properties
% 3.37/0.99  
% 3.37/0.99  clauses:                                16
% 3.37/0.99  conjectures:                            1
% 3.37/0.99  epr:                                    1
% 3.37/0.99  horn:                                   12
% 3.37/0.99  ground:                                 2
% 3.37/0.99  unary:                                  4
% 3.37/0.99  binary:                                 4
% 3.37/0.99  lits:                                   41
% 3.37/0.99  lits_eq:                                6
% 3.37/0.99  fd_pure:                                0
% 3.37/0.99  fd_pseudo:                              0
% 3.37/0.99  fd_cond:                                1
% 3.37/0.99  fd_pseudo_cond:                         0
% 3.37/0.99  ac_symbols:                             0
% 3.37/0.99  
% 3.37/0.99  ------ Propositional Solver
% 3.37/0.99  
% 3.37/0.99  prop_solver_calls:                      29
% 3.37/0.99  prop_fast_solver_calls:                 1240
% 3.37/0.99  smt_solver_calls:                       0
% 3.37/0.99  smt_fast_solver_calls:                  0
% 3.37/0.99  prop_num_of_clauses:                    4835
% 3.37/0.99  prop_preprocess_simplified:             8018
% 3.37/0.99  prop_fo_subsumed:                       64
% 3.37/0.99  prop_solver_time:                       0.
% 3.37/0.99  smt_solver_time:                        0.
% 3.37/0.99  smt_fast_solver_time:                   0.
% 3.37/0.99  prop_fast_solver_time:                  0.
% 3.37/0.99  prop_unsat_core_time:                   0.
% 3.37/0.99  
% 3.37/0.99  ------ QBF
% 3.37/0.99  
% 3.37/0.99  qbf_q_res:                              0
% 3.37/0.99  qbf_num_tautologies:                    0
% 3.37/0.99  qbf_prep_cycles:                        0
% 3.37/0.99  
% 3.37/0.99  ------ BMC1
% 3.37/0.99  
% 3.37/0.99  bmc1_current_bound:                     -1
% 3.37/0.99  bmc1_last_solved_bound:                 -1
% 3.37/0.99  bmc1_unsat_core_size:                   -1
% 3.37/0.99  bmc1_unsat_core_parents_size:           -1
% 3.37/0.99  bmc1_merge_next_fun:                    0
% 3.37/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation
% 3.37/0.99  
% 3.37/0.99  inst_num_of_clauses:                    1352
% 3.37/0.99  inst_num_in_passive:                    283
% 3.37/0.99  inst_num_in_active:                     780
% 3.37/0.99  inst_num_in_unprocessed:                289
% 3.37/0.99  inst_num_of_loops:                      810
% 3.37/0.99  inst_num_of_learning_restarts:          0
% 3.37/0.99  inst_num_moves_active_passive:          25
% 3.37/0.99  inst_lit_activity:                      0
% 3.37/0.99  inst_lit_activity_moves:                0
% 3.37/0.99  inst_num_tautologies:                   0
% 3.37/0.99  inst_num_prop_implied:                  0
% 3.37/0.99  inst_num_existing_simplified:           0
% 3.37/0.99  inst_num_eq_res_simplified:             0
% 3.37/0.99  inst_num_child_elim:                    0
% 3.37/0.99  inst_num_of_dismatching_blockings:      474
% 3.37/0.99  inst_num_of_non_proper_insts:           1288
% 3.37/0.99  inst_num_of_duplicates:                 0
% 3.37/0.99  inst_inst_num_from_inst_to_res:         0
% 3.37/0.99  inst_dismatching_checking_time:         0.
% 3.37/0.99  
% 3.37/0.99  ------ Resolution
% 3.37/0.99  
% 3.37/0.99  res_num_of_clauses:                     0
% 3.37/0.99  res_num_in_passive:                     0
% 3.37/0.99  res_num_in_active:                      0
% 3.37/0.99  res_num_of_loops:                       101
% 3.37/0.99  res_forward_subset_subsumed:            137
% 3.37/0.99  res_backward_subset_subsumed:           0
% 3.37/0.99  res_forward_subsumed:                   0
% 3.37/0.99  res_backward_subsumed:                  0
% 3.37/0.99  res_forward_subsumption_resolution:     3
% 3.37/0.99  res_backward_subsumption_resolution:    0
% 3.37/0.99  res_clause_to_clause_subsumption:       2440
% 3.37/0.99  res_orphan_elimination:                 0
% 3.37/0.99  res_tautology_del:                      124
% 3.37/0.99  res_num_eq_res_simplified:              0
% 3.37/0.99  res_num_sel_changes:                    0
% 3.37/0.99  res_moves_from_active_to_pass:          0
% 3.37/0.99  
% 3.37/0.99  ------ Superposition
% 3.37/0.99  
% 3.37/0.99  sup_time_total:                         0.
% 3.37/0.99  sup_time_generating:                    0.
% 3.37/0.99  sup_time_sim_full:                      0.
% 3.37/0.99  sup_time_sim_immed:                     0.
% 3.37/0.99  
% 3.37/0.99  sup_num_of_clauses:                     272
% 3.37/0.99  sup_num_in_active:                      157
% 3.37/0.99  sup_num_in_passive:                     115
% 3.37/0.99  sup_num_of_loops:                       161
% 3.37/0.99  sup_fw_superposition:                   231
% 3.37/0.99  sup_bw_superposition:                   80
% 3.37/0.99  sup_immediate_simplified:               78
% 3.37/0.99  sup_given_eliminated:                   0
% 3.37/0.99  comparisons_done:                       0
% 3.37/0.99  comparisons_avoided:                    12
% 3.37/0.99  
% 3.37/0.99  ------ Simplifications
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  sim_fw_subset_subsumed:                 11
% 3.37/0.99  sim_bw_subset_subsumed:                 2
% 3.37/0.99  sim_fw_subsumed:                        9
% 3.37/0.99  sim_bw_subsumed:                        2
% 3.37/0.99  sim_fw_subsumption_res:                 6
% 3.37/0.99  sim_bw_subsumption_res:                 1
% 3.37/0.99  sim_tautology_del:                      2
% 3.37/0.99  sim_eq_tautology_del:                   1
% 3.37/0.99  sim_eq_res_simp:                        0
% 3.37/0.99  sim_fw_demodulated:                     7
% 3.37/0.99  sim_bw_demodulated:                     4
% 3.37/0.99  sim_light_normalised:                   59
% 3.37/0.99  sim_joinable_taut:                      0
% 3.37/0.99  sim_joinable_simp:                      0
% 3.37/0.99  sim_ac_normalised:                      0
% 3.37/0.99  sim_smt_subsumption:                    0
% 3.37/0.99  
%------------------------------------------------------------------------------
