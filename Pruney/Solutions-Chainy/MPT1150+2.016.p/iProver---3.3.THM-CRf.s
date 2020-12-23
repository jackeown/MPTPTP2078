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

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 457 expanded)
%              Number of clauses        :   64 ( 131 expanded)
%              Number of leaves         :   15 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          :  494 (2208 expanded)
%              Number of equality atoms :  114 ( 403 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
    inference(rectify,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,
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

fof(f38,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f37])).

fof(f60,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1107,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1107,c_0])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1106,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_469,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_470,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_23,c_22,c_21,c_19])).

cnf(c_1102,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_288,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_637,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_288,c_19])).

cnf(c_638,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_1151,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1102,c_638])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_274,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_609,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_23])).

cnf(c_610,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_48,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_63,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_612,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_23,c_19,c_48,c_63])).

cnf(c_622,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_612])).

cnf(c_623,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_1097,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_1117,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1097,c_638])).

cnf(c_1361,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1117])).

cnf(c_15,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_418,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_419,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_423,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_23,c_22,c_21,c_19])).

cnf(c_1104,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_1185,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1104,c_638])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_642,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_643,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_1096,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_1122,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1096,c_638])).

cnf(c_1617,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1122])).

cnf(c_1953,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1617,c_1151])).

cnf(c_1954,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1953])).

cnf(c_1962,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1954])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_23,c_22,c_21,c_19])).

cnf(c_1098,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_1127,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1098,c_638])).

cnf(c_1538,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1114,c_1127])).

cnf(c_1963,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1962,c_1538])).

cnf(c_3023,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1963,c_1114])).

cnf(c_3027,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_3023])).

cnf(c_3048,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1114,c_3027])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3126,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3048,c_18])).

cnf(c_3127,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3126])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.22/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.02  
% 2.22/1.02  ------  iProver source info
% 2.22/1.02  
% 2.22/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.02  git: non_committed_changes: false
% 2.22/1.02  git: last_make_outside_of_git: false
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     num_symb
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       true
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  ------ Parsing...
% 2.22/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.02  ------ Proving...
% 2.22/1.02  ------ Problem Properties 
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  clauses                                 15
% 2.22/1.02  conjectures                             1
% 2.22/1.02  EPR                                     0
% 2.22/1.02  Horn                                    11
% 2.22/1.02  unary                                   4
% 2.22/1.02  binary                                  3
% 2.22/1.02  lits                                    39
% 2.22/1.02  lits eq                                 7
% 2.22/1.02  fd_pure                                 0
% 2.22/1.02  fd_pseudo                               0
% 2.22/1.02  fd_cond                                 2
% 2.22/1.02  fd_pseudo_cond                          0
% 2.22/1.02  AC symbols                              0
% 2.22/1.02  
% 2.22/1.02  ------ Schedule dynamic 5 is on 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ 
% 2.22/1.02  Current options:
% 2.22/1.02  ------ 
% 2.22/1.02  
% 2.22/1.02  ------ Input Options
% 2.22/1.02  
% 2.22/1.02  --out_options                           all
% 2.22/1.02  --tptp_safe_out                         true
% 2.22/1.02  --problem_path                          ""
% 2.22/1.02  --include_path                          ""
% 2.22/1.02  --clausifier                            res/vclausify_rel
% 2.22/1.02  --clausifier_options                    --mode clausify
% 2.22/1.02  --stdin                                 false
% 2.22/1.02  --stats_out                             all
% 2.22/1.02  
% 2.22/1.02  ------ General Options
% 2.22/1.02  
% 2.22/1.02  --fof                                   false
% 2.22/1.02  --time_out_real                         305.
% 2.22/1.02  --time_out_virtual                      -1.
% 2.22/1.02  --symbol_type_check                     false
% 2.22/1.02  --clausify_out                          false
% 2.22/1.02  --sig_cnt_out                           false
% 2.22/1.02  --trig_cnt_out                          false
% 2.22/1.02  --trig_cnt_out_tolerance                1.
% 2.22/1.02  --trig_cnt_out_sk_spl                   false
% 2.22/1.02  --abstr_cl_out                          false
% 2.22/1.02  
% 2.22/1.02  ------ Global Options
% 2.22/1.02  
% 2.22/1.02  --schedule                              default
% 2.22/1.02  --add_important_lit                     false
% 2.22/1.02  --prop_solver_per_cl                    1000
% 2.22/1.02  --min_unsat_core                        false
% 2.22/1.02  --soft_assumptions                      false
% 2.22/1.02  --soft_lemma_size                       3
% 2.22/1.02  --prop_impl_unit_size                   0
% 2.22/1.02  --prop_impl_unit                        []
% 2.22/1.02  --share_sel_clauses                     true
% 2.22/1.02  --reset_solvers                         false
% 2.22/1.02  --bc_imp_inh                            [conj_cone]
% 2.22/1.02  --conj_cone_tolerance                   3.
% 2.22/1.02  --extra_neg_conj                        none
% 2.22/1.02  --large_theory_mode                     true
% 2.22/1.02  --prolific_symb_bound                   200
% 2.22/1.02  --lt_threshold                          2000
% 2.22/1.02  --clause_weak_htbl                      true
% 2.22/1.02  --gc_record_bc_elim                     false
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing Options
% 2.22/1.02  
% 2.22/1.02  --preprocessing_flag                    true
% 2.22/1.02  --time_out_prep_mult                    0.1
% 2.22/1.02  --splitting_mode                        input
% 2.22/1.02  --splitting_grd                         true
% 2.22/1.02  --splitting_cvd                         false
% 2.22/1.02  --splitting_cvd_svl                     false
% 2.22/1.02  --splitting_nvd                         32
% 2.22/1.02  --sub_typing                            true
% 2.22/1.02  --prep_gs_sim                           true
% 2.22/1.02  --prep_unflatten                        true
% 2.22/1.02  --prep_res_sim                          true
% 2.22/1.02  --prep_upred                            true
% 2.22/1.02  --prep_sem_filter                       exhaustive
% 2.22/1.02  --prep_sem_filter_out                   false
% 2.22/1.02  --pred_elim                             true
% 2.22/1.02  --res_sim_input                         true
% 2.22/1.02  --eq_ax_congr_red                       true
% 2.22/1.02  --pure_diseq_elim                       true
% 2.22/1.02  --brand_transform                       false
% 2.22/1.02  --non_eq_to_eq                          false
% 2.22/1.02  --prep_def_merge                        true
% 2.22/1.02  --prep_def_merge_prop_impl              false
% 2.22/1.02  --prep_def_merge_mbd                    true
% 2.22/1.02  --prep_def_merge_tr_red                 false
% 2.22/1.02  --prep_def_merge_tr_cl                  false
% 2.22/1.02  --smt_preprocessing                     true
% 2.22/1.02  --smt_ac_axioms                         fast
% 2.22/1.02  --preprocessed_out                      false
% 2.22/1.02  --preprocessed_stats                    false
% 2.22/1.02  
% 2.22/1.02  ------ Abstraction refinement Options
% 2.22/1.02  
% 2.22/1.02  --abstr_ref                             []
% 2.22/1.02  --abstr_ref_prep                        false
% 2.22/1.02  --abstr_ref_until_sat                   false
% 2.22/1.02  --abstr_ref_sig_restrict                funpre
% 2.22/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.02  --abstr_ref_under                       []
% 2.22/1.02  
% 2.22/1.02  ------ SAT Options
% 2.22/1.02  
% 2.22/1.02  --sat_mode                              false
% 2.22/1.02  --sat_fm_restart_options                ""
% 2.22/1.02  --sat_gr_def                            false
% 2.22/1.02  --sat_epr_types                         true
% 2.22/1.02  --sat_non_cyclic_types                  false
% 2.22/1.02  --sat_finite_models                     false
% 2.22/1.02  --sat_fm_lemmas                         false
% 2.22/1.02  --sat_fm_prep                           false
% 2.22/1.02  --sat_fm_uc_incr                        true
% 2.22/1.02  --sat_out_model                         small
% 2.22/1.02  --sat_out_clauses                       false
% 2.22/1.02  
% 2.22/1.02  ------ QBF Options
% 2.22/1.02  
% 2.22/1.02  --qbf_mode                              false
% 2.22/1.02  --qbf_elim_univ                         false
% 2.22/1.02  --qbf_dom_inst                          none
% 2.22/1.02  --qbf_dom_pre_inst                      false
% 2.22/1.02  --qbf_sk_in                             false
% 2.22/1.02  --qbf_pred_elim                         true
% 2.22/1.02  --qbf_split                             512
% 2.22/1.02  
% 2.22/1.02  ------ BMC1 Options
% 2.22/1.02  
% 2.22/1.02  --bmc1_incremental                      false
% 2.22/1.02  --bmc1_axioms                           reachable_all
% 2.22/1.02  --bmc1_min_bound                        0
% 2.22/1.02  --bmc1_max_bound                        -1
% 2.22/1.02  --bmc1_max_bound_default                -1
% 2.22/1.02  --bmc1_symbol_reachability              true
% 2.22/1.02  --bmc1_property_lemmas                  false
% 2.22/1.02  --bmc1_k_induction                      false
% 2.22/1.02  --bmc1_non_equiv_states                 false
% 2.22/1.02  --bmc1_deadlock                         false
% 2.22/1.02  --bmc1_ucm                              false
% 2.22/1.02  --bmc1_add_unsat_core                   none
% 2.22/1.02  --bmc1_unsat_core_children              false
% 2.22/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.02  --bmc1_out_stat                         full
% 2.22/1.02  --bmc1_ground_init                      false
% 2.22/1.02  --bmc1_pre_inst_next_state              false
% 2.22/1.02  --bmc1_pre_inst_state                   false
% 2.22/1.02  --bmc1_pre_inst_reach_state             false
% 2.22/1.02  --bmc1_out_unsat_core                   false
% 2.22/1.02  --bmc1_aig_witness_out                  false
% 2.22/1.02  --bmc1_verbose                          false
% 2.22/1.02  --bmc1_dump_clauses_tptp                false
% 2.22/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.02  --bmc1_dump_file                        -
% 2.22/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.02  --bmc1_ucm_extend_mode                  1
% 2.22/1.02  --bmc1_ucm_init_mode                    2
% 2.22/1.02  --bmc1_ucm_cone_mode                    none
% 2.22/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.02  --bmc1_ucm_relax_model                  4
% 2.22/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.02  --bmc1_ucm_layered_model                none
% 2.22/1.02  --bmc1_ucm_max_lemma_size               10
% 2.22/1.02  
% 2.22/1.02  ------ AIG Options
% 2.22/1.02  
% 2.22/1.02  --aig_mode                              false
% 2.22/1.02  
% 2.22/1.02  ------ Instantiation Options
% 2.22/1.02  
% 2.22/1.02  --instantiation_flag                    true
% 2.22/1.02  --inst_sos_flag                         false
% 2.22/1.02  --inst_sos_phase                        true
% 2.22/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.02  --inst_lit_sel_side                     none
% 2.22/1.02  --inst_solver_per_active                1400
% 2.22/1.02  --inst_solver_calls_frac                1.
% 2.22/1.02  --inst_passive_queue_type               priority_queues
% 2.22/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.02  --inst_passive_queues_freq              [25;2]
% 2.22/1.02  --inst_dismatching                      true
% 2.22/1.02  --inst_eager_unprocessed_to_passive     true
% 2.22/1.02  --inst_prop_sim_given                   true
% 2.22/1.02  --inst_prop_sim_new                     false
% 2.22/1.02  --inst_subs_new                         false
% 2.22/1.02  --inst_eq_res_simp                      false
% 2.22/1.02  --inst_subs_given                       false
% 2.22/1.02  --inst_orphan_elimination               true
% 2.22/1.02  --inst_learning_loop_flag               true
% 2.22/1.02  --inst_learning_start                   3000
% 2.22/1.02  --inst_learning_factor                  2
% 2.22/1.02  --inst_start_prop_sim_after_learn       3
% 2.22/1.02  --inst_sel_renew                        solver
% 2.22/1.02  --inst_lit_activity_flag                true
% 2.22/1.02  --inst_restr_to_given                   false
% 2.22/1.02  --inst_activity_threshold               500
% 2.22/1.02  --inst_out_proof                        true
% 2.22/1.02  
% 2.22/1.02  ------ Resolution Options
% 2.22/1.02  
% 2.22/1.02  --resolution_flag                       false
% 2.22/1.02  --res_lit_sel                           adaptive
% 2.22/1.02  --res_lit_sel_side                      none
% 2.22/1.02  --res_ordering                          kbo
% 2.22/1.02  --res_to_prop_solver                    active
% 2.22/1.02  --res_prop_simpl_new                    false
% 2.22/1.02  --res_prop_simpl_given                  true
% 2.22/1.02  --res_passive_queue_type                priority_queues
% 2.22/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.02  --res_passive_queues_freq               [15;5]
% 2.22/1.02  --res_forward_subs                      full
% 2.22/1.02  --res_backward_subs                     full
% 2.22/1.02  --res_forward_subs_resolution           true
% 2.22/1.02  --res_backward_subs_resolution          true
% 2.22/1.02  --res_orphan_elimination                true
% 2.22/1.02  --res_time_limit                        2.
% 2.22/1.02  --res_out_proof                         true
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Options
% 2.22/1.02  
% 2.22/1.02  --superposition_flag                    true
% 2.22/1.02  --sup_passive_queue_type                priority_queues
% 2.22/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.02  --demod_completeness_check              fast
% 2.22/1.02  --demod_use_ground                      true
% 2.22/1.02  --sup_to_prop_solver                    passive
% 2.22/1.02  --sup_prop_simpl_new                    true
% 2.22/1.02  --sup_prop_simpl_given                  true
% 2.22/1.02  --sup_fun_splitting                     false
% 2.22/1.02  --sup_smt_interval                      50000
% 2.22/1.02  
% 2.22/1.02  ------ Superposition Simplification Setup
% 2.22/1.02  
% 2.22/1.02  --sup_indices_passive                   []
% 2.22/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_full_bw                           [BwDemod]
% 2.22/1.02  --sup_immed_triv                        [TrivRules]
% 2.22/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_immed_bw_main                     []
% 2.22/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.02  
% 2.22/1.02  ------ Combination Options
% 2.22/1.02  
% 2.22/1.02  --comb_res_mult                         3
% 2.22/1.02  --comb_sup_mult                         2
% 2.22/1.02  --comb_inst_mult                        10
% 2.22/1.02  
% 2.22/1.02  ------ Debug Options
% 2.22/1.02  
% 2.22/1.02  --dbg_backtrace                         false
% 2.22/1.02  --dbg_dump_prop_clauses                 false
% 2.22/1.02  --dbg_dump_prop_clauses_file            -
% 2.22/1.02  --dbg_out_stat                          false
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  ------ Proving...
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  % SZS status Theorem for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02   Resolution empty clause
% 2.22/1.02  
% 2.22/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  fof(f2,axiom,(
% 2.22/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f40,plain,(
% 2.22/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.22/1.02    inference(cnf_transformation,[],[f2])).
% 2.22/1.02  
% 2.22/1.02  fof(f1,axiom,(
% 2.22/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f39,plain,(
% 2.22/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.22/1.02    inference(cnf_transformation,[],[f1])).
% 2.22/1.02  
% 2.22/1.02  fof(f3,axiom,(
% 2.22/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f13,plain,(
% 2.22/1.02    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f3])).
% 2.22/1.02  
% 2.22/1.02  fof(f14,plain,(
% 2.22/1.02    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/1.02    inference(flattening,[],[f13])).
% 2.22/1.02  
% 2.22/1.02  fof(f28,plain,(
% 2.22/1.02    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f29,plain,(
% 2.22/1.02    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).
% 2.22/1.02  
% 2.22/1.02  fof(f42,plain,(
% 2.22/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/1.02    inference(cnf_transformation,[],[f29])).
% 2.22/1.02  
% 2.22/1.02  fof(f10,axiom,(
% 2.22/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f24,plain,(
% 2.22/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.22/1.02    inference(ennf_transformation,[],[f10])).
% 2.22/1.02  
% 2.22/1.02  fof(f25,plain,(
% 2.22/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.22/1.02    inference(flattening,[],[f24])).
% 2.22/1.02  
% 2.22/1.02  fof(f32,plain,(
% 2.22/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.22/1.02    inference(nnf_transformation,[],[f25])).
% 2.22/1.02  
% 2.22/1.02  fof(f33,plain,(
% 2.22/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.22/1.02    inference(rectify,[],[f32])).
% 2.22/1.02  
% 2.22/1.02  fof(f35,plain,(
% 2.22/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f34,plain,(
% 2.22/1.02    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f36,plain,(
% 2.22/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).
% 2.22/1.02  
% 2.22/1.02  fof(f51,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f36])).
% 2.22/1.02  
% 2.22/1.02  fof(f11,conjecture,(
% 2.22/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f12,negated_conjecture,(
% 2.22/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.22/1.02    inference(negated_conjecture,[],[f11])).
% 2.22/1.02  
% 2.22/1.02  fof(f26,plain,(
% 2.22/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f12])).
% 2.22/1.02  
% 2.22/1.02  fof(f27,plain,(
% 2.22/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f26])).
% 2.22/1.02  
% 2.22/1.02  fof(f37,plain,(
% 2.22/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.22/1.02    introduced(choice_axiom,[])).
% 2.22/1.02  
% 2.22/1.02  fof(f38,plain,(
% 2.22/1.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.22/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f37])).
% 2.22/1.02  
% 2.22/1.02  fof(f60,plain,(
% 2.22/1.02    v5_orders_2(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f57,plain,(
% 2.22/1.02    ~v2_struct_0(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f58,plain,(
% 2.22/1.02    v3_orders_2(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f59,plain,(
% 2.22/1.02    v4_orders_2(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f61,plain,(
% 2.22/1.02    l1_orders_2(sK3)),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  fof(f9,axiom,(
% 2.22/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f23,plain,(
% 2.22/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f9])).
% 2.22/1.02  
% 2.22/1.02  fof(f50,plain,(
% 2.22/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f23])).
% 2.22/1.02  
% 2.22/1.02  fof(f5,axiom,(
% 2.22/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f17,plain,(
% 2.22/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f5])).
% 2.22/1.02  
% 2.22/1.02  fof(f44,plain,(
% 2.22/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f17])).
% 2.22/1.02  
% 2.22/1.02  fof(f4,axiom,(
% 2.22/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f15,plain,(
% 2.22/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.22/1.02    inference(ennf_transformation,[],[f4])).
% 2.22/1.02  
% 2.22/1.02  fof(f16,plain,(
% 2.22/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.22/1.02    inference(flattening,[],[f15])).
% 2.22/1.02  
% 2.22/1.02  fof(f43,plain,(
% 2.22/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f16])).
% 2.22/1.02  
% 2.22/1.02  fof(f6,axiom,(
% 2.22/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f18,plain,(
% 2.22/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f6])).
% 2.22/1.02  
% 2.22/1.02  fof(f19,plain,(
% 2.22/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f18])).
% 2.22/1.02  
% 2.22/1.02  fof(f45,plain,(
% 2.22/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f19])).
% 2.22/1.02  
% 2.22/1.02  fof(f53,plain,(
% 2.22/1.02    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f36])).
% 2.22/1.02  
% 2.22/1.02  fof(f7,axiom,(
% 2.22/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f20,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.22/1.02    inference(ennf_transformation,[],[f7])).
% 2.22/1.02  
% 2.22/1.02  fof(f30,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.22/1.02    inference(nnf_transformation,[],[f20])).
% 2.22/1.02  
% 2.22/1.02  fof(f31,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.22/1.02    inference(flattening,[],[f30])).
% 2.22/1.02  
% 2.22/1.02  fof(f47,plain,(
% 2.22/1.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f31])).
% 2.22/1.02  
% 2.22/1.02  fof(f63,plain,(
% 2.22/1.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.22/1.02    inference(equality_resolution,[],[f47])).
% 2.22/1.02  
% 2.22/1.02  fof(f8,axiom,(
% 2.22/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 2.22/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/1.02  
% 2.22/1.02  fof(f21,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.22/1.02    inference(ennf_transformation,[],[f8])).
% 2.22/1.02  
% 2.22/1.02  fof(f22,plain,(
% 2.22/1.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.22/1.02    inference(flattening,[],[f21])).
% 2.22/1.02  
% 2.22/1.02  fof(f49,plain,(
% 2.22/1.02    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/1.02    inference(cnf_transformation,[],[f22])).
% 2.22/1.02  
% 2.22/1.02  fof(f62,plain,(
% 2.22/1.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 2.22/1.02    inference(cnf_transformation,[],[f38])).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1,plain,
% 2.22/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.22/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1107,plain,
% 2.22/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_0,plain,
% 2.22/1.02      ( k2_subset_1(X0) = X0 ),
% 2.22/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1114,plain,
% 2.22/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1107,c_0]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_2,plain,
% 2.22/1.02      ( r2_hidden(sK0(X0,X1),X1)
% 2.22/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 2.22/1.02      | k1_xboole_0 = X1 ),
% 2.22/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1106,plain,
% 2.22/1.02      ( k1_xboole_0 = X0
% 2.22/1.02      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.22/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_17,plain,
% 2.22/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_orders_2(X1)
% 2.22/1.02      | ~ v4_orders_2(X1)
% 2.22/1.02      | ~ v5_orders_2(X1)
% 2.22/1.02      | ~ l1_orders_2(X1)
% 2.22/1.02      | v2_struct_0(X1) ),
% 2.22/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_20,negated_conjecture,
% 2.22/1.02      ( v5_orders_2(sK3) ),
% 2.22/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_469,plain,
% 2.22/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 2.22/1.02      | ~ v3_orders_2(X1)
% 2.22/1.02      | ~ v4_orders_2(X1)
% 2.22/1.02      | ~ l1_orders_2(X1)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | sK3 != X1 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_470,plain,
% 2.22/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.22/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 2.22/1.02      | ~ v3_orders_2(sK3)
% 2.22/1.02      | ~ v4_orders_2(sK3)
% 2.22/1.02      | ~ l1_orders_2(sK3)
% 2.22/1.02      | v2_struct_0(sK3) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_469]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_23,negated_conjecture,
% 2.22/1.02      ( ~ v2_struct_0(sK3) ),
% 2.22/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_22,negated_conjecture,
% 2.22/1.02      ( v3_orders_2(sK3) ),
% 2.22/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_21,negated_conjecture,
% 2.22/1.02      ( v4_orders_2(sK3) ),
% 2.22/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_19,negated_conjecture,
% 2.22/1.02      ( l1_orders_2(sK3) ),
% 2.22/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_474,plain,
% 2.22/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.22/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
% 2.22/1.02      inference(global_propositional_subsumption,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_470,c_23,c_22,c_21,c_19]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1102,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.22/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.22/1.02      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_11,plain,
% 2.22/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.22/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_5,plain,
% 2.22/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.22/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_288,plain,
% 2.22/1.02      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.22/1.02      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_637,plain,
% 2.22/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_288,c_19]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_638,plain,
% 2.22/1.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_637]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1151,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.22/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.22/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1102,c_638]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_4,plain,
% 2.22/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.22/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_6,plain,
% 2.22/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.22/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_274,plain,
% 2.22/1.02      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.22/1.02      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_609,plain,
% 2.22/1.02      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_274,c_23]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_610,plain,
% 2.22/1.02      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_609]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_48,plain,
% 2.22/1.02      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_63,plain,
% 2.22/1.02      ( v2_struct_0(sK3)
% 2.22/1.02      | ~ l1_struct_0(sK3)
% 2.22/1.02      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.22/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_612,plain,
% 2.22/1.02      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.22/1.02      inference(global_propositional_subsumption,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_610,c_23,c_19,c_48,c_63]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_622,plain,
% 2.22/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | u1_struct_0(sK3) != X1 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_612]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_623,plain,
% 2.22/1.02      ( r2_hidden(X0,u1_struct_0(sK3)) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_622]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1097,plain,
% 2.22/1.02      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.22/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1117,plain,
% 2.22/1.02      ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 2.22/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1097,c_638]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1361,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.22/1.02      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 2.22/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1151,c_1117]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_15,plain,
% 2.22/1.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.22/1.02      | ~ r2_hidden(X1,X3)
% 2.22/1.02      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ v3_orders_2(X0)
% 2.22/1.02      | ~ v4_orders_2(X0)
% 2.22/1.02      | ~ v5_orders_2(X0)
% 2.22/1.02      | ~ l1_orders_2(X0)
% 2.22/1.02      | v2_struct_0(X0) ),
% 2.22/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_418,plain,
% 2.22/1.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.22/1.02      | ~ r2_hidden(X1,X3)
% 2.22/1.02      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/1.02      | ~ v3_orders_2(X0)
% 2.22/1.02      | ~ v4_orders_2(X0)
% 2.22/1.02      | ~ l1_orders_2(X0)
% 2.22/1.02      | v2_struct_0(X0)
% 2.22/1.02      | sK3 != X0 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_419,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.22/1.02      | ~ r2_hidden(X0,X2)
% 2.22/1.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.22/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | ~ v3_orders_2(sK3)
% 2.22/1.02      | ~ v4_orders_2(sK3)
% 2.22/1.02      | ~ l1_orders_2(sK3)
% 2.22/1.02      | v2_struct_0(sK3) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_418]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_423,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.22/1.02      | ~ r2_hidden(X0,X2)
% 2.22/1.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.22/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.22/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.22/1.02      inference(global_propositional_subsumption,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_419,c_23,c_22,c_21,c_19]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1104,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.22/1.02      | r2_hidden(X0,X2) != iProver_top
% 2.22/1.02      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 2.22/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.22/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1185,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.22/1.02      | r2_hidden(X0,X2) != iProver_top
% 2.22/1.02      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 2.22/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.22/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1104,c_638]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_8,plain,
% 2.22/1.02      ( ~ r2_orders_2(X0,X1,X1)
% 2.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.02      | ~ l1_orders_2(X0) ),
% 2.22/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_642,plain,
% 2.22/1.02      ( ~ r2_orders_2(X0,X1,X1)
% 2.22/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/1.02      | sK3 != X0 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_643,plain,
% 2.22/1.02      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_642]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1096,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.22/1.02      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1122,plain,
% 2.22/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.22/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1096,c_638]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1617,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.22/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.22/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.22/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1185,c_1122]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1953,plain,
% 2.22/1.02      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.22/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.22/1.02      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 2.22/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1617,c_1151]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1954,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.22/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.22/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(renaming,[status(thm)],[c_1953]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1962,plain,
% 2.22/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.22/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1361,c_1954]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_10,plain,
% 2.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.02      | ~ v3_orders_2(X1)
% 2.22/1.02      | ~ v4_orders_2(X1)
% 2.22/1.02      | ~ v5_orders_2(X1)
% 2.22/1.02      | ~ l1_orders_2(X1)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 2.22/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_559,plain,
% 2.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/1.02      | ~ v3_orders_2(X1)
% 2.22/1.02      | ~ v4_orders_2(X1)
% 2.22/1.02      | ~ l1_orders_2(X1)
% 2.22/1.02      | v2_struct_0(X1)
% 2.22/1.02      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 2.22/1.02      | sK3 != X1 ),
% 2.22/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_560,plain,
% 2.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | ~ v3_orders_2(sK3)
% 2.22/1.02      | ~ v4_orders_2(sK3)
% 2.22/1.02      | ~ l1_orders_2(sK3)
% 2.22/1.02      | v2_struct_0(sK3)
% 2.22/1.02      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.22/1.02      inference(unflattening,[status(thm)],[c_559]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_564,plain,
% 2.22/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.22/1.02      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.22/1.02      inference(global_propositional_subsumption,
% 2.22/1.02                [status(thm)],
% 2.22/1.02                [c_560,c_23,c_22,c_21,c_19]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1098,plain,
% 2.22/1.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.22/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1127,plain,
% 2.22/1.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.22/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1098,c_638]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1538,plain,
% 2.22/1.02      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1114,c_1127]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_1963,plain,
% 2.22/1.02      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.22/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(light_normalisation,[status(thm)],[c_1962,c_1538]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3023,plain,
% 2.22/1.02      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.22/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1963,c_1114]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3027,plain,
% 2.22/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 2.22/1.02      | m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1106,c_3023]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3048,plain,
% 2.22/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.22/1.02      inference(superposition,[status(thm)],[c_1114,c_3027]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_18,negated_conjecture,
% 2.22/1.02      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.22/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3126,plain,
% 2.22/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 2.22/1.02      inference(demodulation,[status(thm)],[c_3048,c_18]) ).
% 2.22/1.02  
% 2.22/1.02  cnf(c_3127,plain,
% 2.22/1.02      ( $false ),
% 2.22/1.02      inference(equality_resolution_simp,[status(thm)],[c_3126]) ).
% 2.22/1.02  
% 2.22/1.02  
% 2.22/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.02  
% 2.22/1.02  ------                               Statistics
% 2.22/1.02  
% 2.22/1.02  ------ General
% 2.22/1.02  
% 2.22/1.02  abstr_ref_over_cycles:                  0
% 2.22/1.02  abstr_ref_under_cycles:                 0
% 2.22/1.02  gc_basic_clause_elim:                   0
% 2.22/1.02  forced_gc_time:                         0
% 2.22/1.02  parsing_time:                           0.017
% 2.22/1.02  unif_index_cands_time:                  0.
% 2.22/1.02  unif_index_add_time:                    0.
% 2.22/1.02  orderings_time:                         0.
% 2.22/1.02  out_proof_time:                         0.008
% 2.22/1.02  total_time:                             0.154
% 2.22/1.02  num_of_symbols:                         53
% 2.22/1.02  num_of_terms:                           2961
% 2.22/1.02  
% 2.22/1.02  ------ Preprocessing
% 2.22/1.02  
% 2.22/1.02  num_of_splits:                          0
% 2.22/1.02  num_of_split_atoms:                     0
% 2.22/1.02  num_of_reused_defs:                     0
% 2.22/1.02  num_eq_ax_congr_red:                    33
% 2.22/1.02  num_of_sem_filtered_clauses:            1
% 2.22/1.02  num_of_subtypes:                        0
% 2.22/1.02  monotx_restored_types:                  0
% 2.22/1.02  sat_num_of_epr_types:                   0
% 2.22/1.02  sat_num_of_non_cyclic_types:            0
% 2.22/1.02  sat_guarded_non_collapsed_types:        0
% 2.22/1.02  num_pure_diseq_elim:                    0
% 2.22/1.02  simp_replaced_by:                       0
% 2.22/1.02  res_preprocessed:                       94
% 2.22/1.02  prep_upred:                             0
% 2.22/1.02  prep_unflattend:                        27
% 2.22/1.02  smt_new_axioms:                         0
% 2.22/1.02  pred_elim_cands:                        3
% 2.22/1.02  pred_elim:                              8
% 2.22/1.02  pred_elim_cl:                           9
% 2.22/1.02  pred_elim_cycles:                       13
% 2.22/1.02  merged_defs:                            0
% 2.22/1.02  merged_defs_ncl:                        0
% 2.22/1.02  bin_hyper_res:                          0
% 2.22/1.02  prep_cycles:                            4
% 2.22/1.02  pred_elim_time:                         0.015
% 2.22/1.02  splitting_time:                         0.
% 2.22/1.02  sem_filter_time:                        0.
% 2.22/1.02  monotx_time:                            0.001
% 2.22/1.02  subtype_inf_time:                       0.
% 2.22/1.02  
% 2.22/1.02  ------ Problem properties
% 2.22/1.02  
% 2.22/1.02  clauses:                                15
% 2.22/1.02  conjectures:                            1
% 2.22/1.02  epr:                                    0
% 2.22/1.02  horn:                                   11
% 2.22/1.02  ground:                                 2
% 2.22/1.02  unary:                                  4
% 2.22/1.02  binary:                                 3
% 2.22/1.02  lits:                                   39
% 2.22/1.02  lits_eq:                                7
% 2.22/1.02  fd_pure:                                0
% 2.22/1.02  fd_pseudo:                              0
% 2.22/1.02  fd_cond:                                2
% 2.22/1.02  fd_pseudo_cond:                         0
% 2.22/1.02  ac_symbols:                             0
% 2.22/1.02  
% 2.22/1.02  ------ Propositional Solver
% 2.22/1.02  
% 2.22/1.02  prop_solver_calls:                      29
% 2.22/1.02  prop_fast_solver_calls:                 873
% 2.22/1.02  smt_solver_calls:                       0
% 2.22/1.02  smt_fast_solver_calls:                  0
% 2.22/1.02  prop_num_of_clauses:                    957
% 2.22/1.02  prop_preprocess_simplified:             3569
% 2.22/1.02  prop_fo_subsumed:                       39
% 2.22/1.02  prop_solver_time:                       0.
% 2.22/1.02  smt_solver_time:                        0.
% 2.22/1.02  smt_fast_solver_time:                   0.
% 2.22/1.02  prop_fast_solver_time:                  0.
% 2.22/1.02  prop_unsat_core_time:                   0.
% 2.22/1.02  
% 2.22/1.02  ------ QBF
% 2.22/1.02  
% 2.22/1.02  qbf_q_res:                              0
% 2.22/1.02  qbf_num_tautologies:                    0
% 2.22/1.03  qbf_prep_cycles:                        0
% 2.22/1.03  
% 2.22/1.03  ------ BMC1
% 2.22/1.03  
% 2.22/1.03  bmc1_current_bound:                     -1
% 2.22/1.03  bmc1_last_solved_bound:                 -1
% 2.22/1.03  bmc1_unsat_core_size:                   -1
% 2.22/1.03  bmc1_unsat_core_parents_size:           -1
% 2.22/1.03  bmc1_merge_next_fun:                    0
% 2.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation
% 2.22/1.03  
% 2.22/1.03  inst_num_of_clauses:                    308
% 2.22/1.03  inst_num_in_passive:                    63
% 2.22/1.03  inst_num_in_active:                     182
% 2.22/1.03  inst_num_in_unprocessed:                63
% 2.22/1.03  inst_num_of_loops:                      190
% 2.22/1.03  inst_num_of_learning_restarts:          0
% 2.22/1.03  inst_num_moves_active_passive:          4
% 2.22/1.03  inst_lit_activity:                      0
% 2.22/1.03  inst_lit_activity_moves:                0
% 2.22/1.03  inst_num_tautologies:                   0
% 2.22/1.03  inst_num_prop_implied:                  0
% 2.22/1.03  inst_num_existing_simplified:           0
% 2.22/1.03  inst_num_eq_res_simplified:             0
% 2.22/1.03  inst_num_child_elim:                    0
% 2.22/1.03  inst_num_of_dismatching_blockings:      137
% 2.22/1.03  inst_num_of_non_proper_insts:           359
% 2.22/1.03  inst_num_of_duplicates:                 0
% 2.22/1.03  inst_inst_num_from_inst_to_res:         0
% 2.22/1.03  inst_dismatching_checking_time:         0.
% 2.22/1.03  
% 2.22/1.03  ------ Resolution
% 2.22/1.03  
% 2.22/1.03  res_num_of_clauses:                     0
% 2.22/1.03  res_num_in_passive:                     0
% 2.22/1.03  res_num_in_active:                      0
% 2.22/1.03  res_num_of_loops:                       98
% 2.22/1.03  res_forward_subset_subsumed:            78
% 2.22/1.03  res_backward_subset_subsumed:           0
% 2.22/1.03  res_forward_subsumed:                   0
% 2.22/1.03  res_backward_subsumed:                  0
% 2.22/1.03  res_forward_subsumption_resolution:     0
% 2.22/1.03  res_backward_subsumption_resolution:    0
% 2.22/1.03  res_clause_to_clause_subsumption:       170
% 2.22/1.03  res_orphan_elimination:                 0
% 2.22/1.03  res_tautology_del:                      55
% 2.22/1.03  res_num_eq_res_simplified:              0
% 2.22/1.03  res_num_sel_changes:                    0
% 2.22/1.03  res_moves_from_active_to_pass:          0
% 2.22/1.03  
% 2.22/1.03  ------ Superposition
% 2.22/1.03  
% 2.22/1.03  sup_time_total:                         0.
% 2.22/1.03  sup_time_generating:                    0.
% 2.22/1.03  sup_time_sim_full:                      0.
% 2.22/1.03  sup_time_sim_immed:                     0.
% 2.22/1.03  
% 2.22/1.03  sup_num_of_clauses:                     41
% 2.22/1.03  sup_num_in_active:                      27
% 2.22/1.03  sup_num_in_passive:                     14
% 2.22/1.03  sup_num_of_loops:                       36
% 2.22/1.03  sup_fw_superposition:                   28
% 2.22/1.03  sup_bw_superposition:                   18
% 2.22/1.03  sup_immediate_simplified:               16
% 2.22/1.03  sup_given_eliminated:                   0
% 2.22/1.03  comparisons_done:                       0
% 2.22/1.03  comparisons_avoided:                    17
% 2.22/1.03  
% 2.22/1.03  ------ Simplifications
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  sim_fw_subset_subsumed:                 1
% 2.22/1.03  sim_bw_subset_subsumed:                 8
% 2.22/1.03  sim_fw_subsumed:                        2
% 2.22/1.03  sim_bw_subsumed:                        2
% 2.22/1.03  sim_fw_subsumption_res:                 2
% 2.22/1.03  sim_bw_subsumption_res:                 1
% 2.22/1.03  sim_tautology_del:                      1
% 2.22/1.03  sim_eq_tautology_del:                   0
% 2.22/1.03  sim_eq_res_simp:                        0
% 2.22/1.03  sim_fw_demodulated:                     1
% 2.22/1.03  sim_bw_demodulated:                     7
% 2.22/1.03  sim_light_normalised:                   21
% 2.22/1.03  sim_joinable_taut:                      0
% 2.22/1.03  sim_joinable_simp:                      0
% 2.22/1.03  sim_ac_normalised:                      0
% 2.22/1.03  sim_smt_subsumption:                    0
% 2.22/1.03  
%------------------------------------------------------------------------------
