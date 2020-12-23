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
% DateTime   : Thu Dec  3 12:12:13 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 818 expanded)
%              Number of clauses        :   76 ( 279 expanded)
%              Number of leaves         :   17 ( 162 expanded)
%              Depth                    :   25
%              Number of atoms          :  573 (3638 expanded)
%              Number of equality atoms :  226 ( 881 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f40])).

fof(f64,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_662,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_669,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1045,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_669])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_677,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1148,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1045,c_677])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_670])).

cnf(c_3449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3392,c_1148])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3821,plain,
    ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3449,c_24,c_25,c_26,c_27,c_28])).

cnf(c_3822,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3821])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_680,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_663,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1447,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_663])).

cnf(c_1456,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1447,c_1148])).

cnf(c_1731,plain,
    ( r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1456,c_24,c_25,c_26,c_27,c_28])).

cnf(c_1732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1731])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_678,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_678])).

cnf(c_47,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_49,plain,
    ( l1_orders_2(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_675,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1445,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_675])).

cnf(c_1800,plain,
    ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1740,c_24,c_28,c_49,c_1445])).

cnf(c_1801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1800])).

cnf(c_15,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_665,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_673,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1814,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_673])).

cnf(c_1959,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1814,c_28])).

cnf(c_1960,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1959])).

cnf(c_1967,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1960])).

cnf(c_3143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_1967])).

cnf(c_3178,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3143,c_1148])).

cnf(c_3709,plain,
    ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3178,c_24,c_25,c_26,c_27,c_28,c_1732])).

cnf(c_3710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3709])).

cnf(c_3718,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_3710])).

cnf(c_4,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_676,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1446,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_676])).

cnf(c_4357,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3718,c_28,c_49,c_1446])).

cnf(c_1600,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_28,c_49])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_671,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3204,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_671])).

cnf(c_3799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3204,c_24,c_25,c_26,c_27,c_28])).

cnf(c_3800,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3799])).

cnf(c_3808,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1600,c_3800])).

cnf(c_4363,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4357,c_3808])).

cnf(c_4368,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_4363])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_218,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_997,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_1039,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_217,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_4575,plain,
    ( m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4368,c_18,c_1039,c_1040])).

cnf(c_4583,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3822,c_4575])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4583,c_1446,c_49,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.72/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.02  
% 3.72/1.02  ------  iProver source info
% 3.72/1.02  
% 3.72/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.02  git: non_committed_changes: false
% 3.72/1.02  git: last_make_outside_of_git: false
% 3.72/1.02  
% 3.72/1.02  ------ 
% 3.72/1.02  ------ Parsing...
% 3.72/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.02  ------ Proving...
% 3.72/1.02  ------ Problem Properties 
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  clauses                                 24
% 3.72/1.02  conjectures                             6
% 3.72/1.02  EPR                                     7
% 3.72/1.02  Horn                                    12
% 3.72/1.02  unary                                   6
% 3.72/1.02  binary                                  3
% 3.72/1.02  lits                                    105
% 3.72/1.02  lits eq                                 7
% 3.72/1.02  fd_pure                                 0
% 3.72/1.02  fd_pseudo                               0
% 3.72/1.02  fd_cond                                 2
% 3.72/1.02  fd_pseudo_cond                          1
% 3.72/1.02  AC symbols                              0
% 3.72/1.02  
% 3.72/1.02  ------ Input Options Time Limit: Unbounded
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  ------ 
% 3.72/1.02  Current options:
% 3.72/1.02  ------ 
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  ------ Proving...
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  % SZS status Theorem for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  fof(f11,conjecture,(
% 3.72/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f12,negated_conjecture,(
% 3.72/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.72/1.02    inference(negated_conjecture,[],[f11])).
% 3.72/1.02  
% 3.72/1.02  fof(f29,plain,(
% 3.72/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.72/1.02    inference(ennf_transformation,[],[f12])).
% 3.72/1.02  
% 3.72/1.02  fof(f30,plain,(
% 3.72/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.72/1.02    inference(flattening,[],[f29])).
% 3.72/1.02  
% 3.72/1.02  fof(f40,plain,(
% 3.72/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  
% 3.72/1.02  fof(f41,plain,(
% 3.72/1.02    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f64,plain,(
% 3.72/1.02    l1_orders_2(sK3)),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  fof(f9,axiom,(
% 3.72/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f26,plain,(
% 3.72/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.72/1.02    inference(ennf_transformation,[],[f9])).
% 3.72/1.02  
% 3.72/1.02  fof(f53,plain,(
% 3.72/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f26])).
% 3.72/1.02  
% 3.72/1.02  fof(f3,axiom,(
% 3.72/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f17,plain,(
% 3.72/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.72/1.02    inference(ennf_transformation,[],[f3])).
% 3.72/1.02  
% 3.72/1.02  fof(f45,plain,(
% 3.72/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f17])).
% 3.72/1.02  
% 3.72/1.02  fof(f8,axiom,(
% 3.72/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f24,plain,(
% 3.72/1.02    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.72/1.02    inference(ennf_transformation,[],[f8])).
% 3.72/1.02  
% 3.72/1.02  fof(f25,plain,(
% 3.72/1.02    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.72/1.02    inference(flattening,[],[f24])).
% 3.72/1.02  
% 3.72/1.02  fof(f52,plain,(
% 3.72/1.02    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f25])).
% 3.72/1.02  
% 3.72/1.02  fof(f60,plain,(
% 3.72/1.02    ~v2_struct_0(sK3)),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  fof(f61,plain,(
% 3.72/1.02    v3_orders_2(sK3)),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  fof(f62,plain,(
% 3.72/1.02    v4_orders_2(sK3)),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  fof(f63,plain,(
% 3.72/1.02    v5_orders_2(sK3)),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  fof(f1,axiom,(
% 3.72/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f13,plain,(
% 3.72/1.02    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/1.02    inference(ennf_transformation,[],[f1])).
% 3.72/1.02  
% 3.72/1.02  fof(f14,plain,(
% 3.72/1.02    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/1.02    inference(flattening,[],[f13])).
% 3.72/1.02  
% 3.72/1.02  fof(f31,plain,(
% 3.72/1.02    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  
% 3.72/1.02  fof(f32,plain,(
% 3.72/1.02    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f31])).
% 3.72/1.02  
% 3.72/1.02  fof(f43,plain,(
% 3.72/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f32])).
% 3.72/1.02  
% 3.72/1.02  fof(f10,axiom,(
% 3.72/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f27,plain,(
% 3.72/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.72/1.02    inference(ennf_transformation,[],[f10])).
% 3.72/1.02  
% 3.72/1.02  fof(f28,plain,(
% 3.72/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.72/1.02    inference(flattening,[],[f27])).
% 3.72/1.02  
% 3.72/1.02  fof(f35,plain,(
% 3.72/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.72/1.02    inference(nnf_transformation,[],[f28])).
% 3.72/1.02  
% 3.72/1.02  fof(f36,plain,(
% 3.72/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.72/1.02    inference(rectify,[],[f35])).
% 3.72/1.02  
% 3.72/1.02  fof(f38,plain,(
% 3.72/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  
% 3.72/1.02  fof(f37,plain,(
% 3.72/1.02    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  
% 3.72/1.02  fof(f39,plain,(
% 3.72/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 3.72/1.02  
% 3.72/1.02  fof(f54,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f39])).
% 3.72/1.02  
% 3.72/1.02  fof(f2,axiom,(
% 3.72/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f15,plain,(
% 3.72/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.72/1.02    inference(ennf_transformation,[],[f2])).
% 3.72/1.02  
% 3.72/1.02  fof(f16,plain,(
% 3.72/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.72/1.02    inference(flattening,[],[f15])).
% 3.72/1.02  
% 3.72/1.02  fof(f44,plain,(
% 3.72/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f16])).
% 3.72/1.02  
% 3.72/1.02  fof(f5,axiom,(
% 3.72/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f19,plain,(
% 3.72/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.72/1.02    inference(ennf_transformation,[],[f5])).
% 3.72/1.02  
% 3.72/1.02  fof(f20,plain,(
% 3.72/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.72/1.02    inference(flattening,[],[f19])).
% 3.72/1.02  
% 3.72/1.02  fof(f47,plain,(
% 3.72/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f20])).
% 3.72/1.02  
% 3.72/1.02  fof(f56,plain,(
% 3.72/1.02    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f39])).
% 3.72/1.02  
% 3.72/1.02  fof(f6,axiom,(
% 3.72/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f21,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.72/1.02    inference(ennf_transformation,[],[f6])).
% 3.72/1.02  
% 3.72/1.02  fof(f33,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.72/1.02    inference(nnf_transformation,[],[f21])).
% 3.72/1.02  
% 3.72/1.02  fof(f34,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.72/1.02    inference(flattening,[],[f33])).
% 3.72/1.02  
% 3.72/1.02  fof(f49,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f34])).
% 3.72/1.02  
% 3.72/1.02  fof(f66,plain,(
% 3.72/1.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.72/1.02    inference(equality_resolution,[],[f49])).
% 3.72/1.02  
% 3.72/1.02  fof(f4,axiom,(
% 3.72/1.02    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f18,plain,(
% 3.72/1.02    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.72/1.02    inference(ennf_transformation,[],[f4])).
% 3.72/1.02  
% 3.72/1.02  fof(f46,plain,(
% 3.72/1.02    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f18])).
% 3.72/1.02  
% 3.72/1.02  fof(f7,axiom,(
% 3.72/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f22,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.72/1.02    inference(ennf_transformation,[],[f7])).
% 3.72/1.02  
% 3.72/1.02  fof(f23,plain,(
% 3.72/1.02    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.72/1.02    inference(flattening,[],[f22])).
% 3.72/1.02  
% 3.72/1.02  fof(f51,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f23])).
% 3.72/1.02  
% 3.72/1.02  fof(f65,plain,(
% 3.72/1.02    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 3.72/1.02    inference(cnf_transformation,[],[f41])).
% 3.72/1.02  
% 3.72/1.02  cnf(c_19,negated_conjecture,
% 3.72/1.02      ( l1_orders_2(sK3) ),
% 3.72/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_662,plain,
% 3.72/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_11,plain,
% 3.72/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_669,plain,
% 3.72/1.02      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1045,plain,
% 3.72/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_662,c_669]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3,plain,
% 3.72/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_677,plain,
% 3.72/1.02      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.72/1.02      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1148,plain,
% 3.72/1.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1045,c_677]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_10,plain,
% 3.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.02      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.02      | ~ v3_orders_2(X1)
% 3.72/1.02      | ~ v4_orders_2(X1)
% 3.72/1.02      | ~ v5_orders_2(X1)
% 3.72/1.02      | ~ l1_orders_2(X1)
% 3.72/1.02      | v2_struct_0(X1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_670,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.72/1.02      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.72/1.02      | v3_orders_2(X1) != iProver_top
% 3.72/1.02      | v4_orders_2(X1) != iProver_top
% 3.72/1.02      | v5_orders_2(X1) != iProver_top
% 3.72/1.02      | l1_orders_2(X1) != iProver_top
% 3.72/1.02      | v2_struct_0(X1) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3392,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_670]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3449,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(light_normalisation,[status(thm)],[c_3392,c_1148]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_23,negated_conjecture,
% 3.72/1.02      ( ~ v2_struct_0(sK3) ),
% 3.72/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_24,plain,
% 3.72/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_22,negated_conjecture,
% 3.72/1.02      ( v3_orders_2(sK3) ),
% 3.72/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_25,plain,
% 3.72/1.02      ( v3_orders_2(sK3) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_21,negated_conjecture,
% 3.72/1.02      ( v4_orders_2(sK3) ),
% 3.72/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_26,plain,
% 3.72/1.02      ( v4_orders_2(sK3) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_20,negated_conjecture,
% 3.72/1.02      ( v5_orders_2(sK3) ),
% 3.72/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_27,plain,
% 3.72/1.02      ( v5_orders_2(sK3) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_28,plain,
% 3.72/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3821,plain,
% 3.72/1.02      ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_3449,c_24,c_25,c_26,c_27,c_28]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3822,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_3821]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_0,plain,
% 3.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/1.02      | r2_hidden(sK0(X1,X0),X0)
% 3.72/1.02      | k1_xboole_0 = X0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_680,plain,
% 3.72/1.02      ( k1_xboole_0 = X0
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/1.02      | r2_hidden(sK0(X1,X0),X0) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_17,plain,
% 3.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.02      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.72/1.02      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.72/1.02      | ~ v3_orders_2(X1)
% 3.72/1.02      | ~ v4_orders_2(X1)
% 3.72/1.02      | ~ v5_orders_2(X1)
% 3.72/1.02      | ~ l1_orders_2(X1)
% 3.72/1.02      | v2_struct_0(X1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_663,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 3.72/1.02      | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
% 3.72/1.02      | v3_orders_2(X1) != iProver_top
% 3.72/1.02      | v4_orders_2(X1) != iProver_top
% 3.72/1.02      | v5_orders_2(X1) != iProver_top
% 3.72/1.02      | l1_orders_2(X1) != iProver_top
% 3.72/1.02      | v2_struct_0(X1) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1447,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_663]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1456,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(light_normalisation,[status(thm)],[c_1447,c_1148]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1731,plain,
% 3.72/1.02      ( r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_1456,c_24,c_25,c_26,c_27,c_28]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1732,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_1731]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_2,plain,
% 3.72/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_678,plain,
% 3.72/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.72/1.02      | r2_hidden(X0,X1) = iProver_top
% 3.72/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1740,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1732,c_678]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_47,plain,
% 3.72/1.02      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_49,plain,
% 3.72/1.02      ( l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(instantiation,[status(thm)],[c_47]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_5,plain,
% 3.72/1.02      ( v2_struct_0(X0)
% 3.72/1.02      | ~ l1_struct_0(X0)
% 3.72/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.72/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_675,plain,
% 3.72/1.02      ( v2_struct_0(X0) = iProver_top
% 3.72/1.02      | l1_struct_0(X0) != iProver_top
% 3.72/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1445,plain,
% 3.72/1.02      ( v2_struct_0(sK3) = iProver_top
% 3.72/1.02      | l1_struct_0(sK3) != iProver_top
% 3.72/1.02      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_675]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1800,plain,
% 3.72/1.02      ( r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_1740,c_24,c_28,c_49,c_1445]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1801,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_1800]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_15,plain,
% 3.72/1.02      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.72/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.72/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.72/1.02      | ~ r2_hidden(X3,X2)
% 3.72/1.02      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.72/1.02      | ~ v3_orders_2(X0)
% 3.72/1.02      | ~ v4_orders_2(X0)
% 3.72/1.02      | ~ v5_orders_2(X0)
% 3.72/1.02      | ~ l1_orders_2(X0)
% 3.72/1.02      | v2_struct_0(X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_665,plain,
% 3.72/1.02      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 3.72/1.02      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.72/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.72/1.02      | r2_hidden(X3,X2) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 3.72/1.02      | v3_orders_2(X0) != iProver_top
% 3.72/1.02      | v4_orders_2(X0) != iProver_top
% 3.72/1.02      | v5_orders_2(X0) != iProver_top
% 3.72/1.02      | l1_orders_2(X0) != iProver_top
% 3.72/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_7,plain,
% 3.72/1.02      ( ~ r2_orders_2(X0,X1,X1)
% 3.72/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.72/1.02      | ~ l1_orders_2(X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_673,plain,
% 3.72/1.02      ( r2_orders_2(X0,X1,X1) != iProver_top
% 3.72/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.72/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1814,plain,
% 3.72/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.72/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_673]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1959,plain,
% 3.72/1.02      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.72/1.02      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_1814,c_28]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1960,plain,
% 3.72/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.72/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_1959]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1967,plain,
% 3.72/1.02      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 3.72/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1732,c_1960]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3143,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_665,c_1967]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3178,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(light_normalisation,[status(thm)],[c_3143,c_1148]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3709,plain,
% 3.72/1.02      ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_3178,c_24,c_25,c_26,c_27,c_28,c_1732]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3710,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.72/1.02      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_3709]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3718,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1801,c_3710]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.72/1.02      | ~ l1_struct_0(X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_676,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.72/1.02      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1446,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.72/1.02      | l1_struct_0(sK3) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_676]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4357,plain,
% 3.72/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_3718,c_28,c_49,c_1446]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1600,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_1446,c_28,c_49]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_9,plain,
% 3.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.02      | ~ v3_orders_2(X1)
% 3.72/1.02      | ~ v4_orders_2(X1)
% 3.72/1.02      | ~ v5_orders_2(X1)
% 3.72/1.02      | ~ l1_orders_2(X1)
% 3.72/1.02      | v2_struct_0(X1)
% 3.72/1.02      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_671,plain,
% 3.72/1.02      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 3.72/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.72/1.02      | v3_orders_2(X0) != iProver_top
% 3.72/1.02      | v4_orders_2(X0) != iProver_top
% 3.72/1.02      | v5_orders_2(X0) != iProver_top
% 3.72/1.02      | l1_orders_2(X0) != iProver_top
% 3.72/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3204,plain,
% 3.72/1.02      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | v3_orders_2(sK3) != iProver_top
% 3.72/1.02      | v4_orders_2(sK3) != iProver_top
% 3.72/1.02      | v5_orders_2(sK3) != iProver_top
% 3.72/1.02      | l1_orders_2(sK3) != iProver_top
% 3.72/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1148,c_671]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3799,plain,
% 3.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.72/1.02      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_3204,c_24,c_25,c_26,c_27,c_28]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3800,plain,
% 3.72/1.02      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.72/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(renaming,[status(thm)],[c_3799]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3808,plain,
% 3.72/1.02      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1600,c_3800]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4363,plain,
% 3.72/1.02      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(light_normalisation,[status(thm)],[c_4357,c_3808]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4368,plain,
% 3.72/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.72/1.02      | m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_680,c_4363]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_18,negated_conjecture,
% 3.72/1.02      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.72/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_218,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_997,plain,
% 3.72/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
% 3.72/1.02      | k1_xboole_0 != X0
% 3.72/1.02      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.72/1.02      inference(instantiation,[status(thm)],[c_218]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1039,plain,
% 3.72/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 3.72/1.02      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 3.72/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.72/1.02      inference(instantiation,[status(thm)],[c_997]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_217,plain,( X0 = X0 ),theory(equality) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1040,plain,
% 3.72/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.72/1.02      inference(instantiation,[status(thm)],[c_217]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4575,plain,
% 3.72/1.02      ( m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
% 3.72/1.02      inference(global_propositional_subsumption,
% 3.72/1.02                [status(thm)],
% 3.72/1.02                [c_4368,c_18,c_1039,c_1040]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_4583,plain,
% 3.72/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_3822,c_4575]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(contradiction,plain,
% 3.72/1.02      ( $false ),
% 3.72/1.02      inference(minisat,[status(thm)],[c_4583,c_1446,c_49,c_28]) ).
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  ------                               Statistics
% 3.72/1.02  
% 3.72/1.02  ------ Selected
% 3.72/1.02  
% 3.72/1.02  total_time:                             0.273
% 3.72/1.02  
%------------------------------------------------------------------------------
