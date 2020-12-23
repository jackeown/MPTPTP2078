%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:12 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  129 (1114 expanded)
%              Number of clauses        :   71 ( 368 expanded)
%              Number of leaves         :   16 ( 224 expanded)
%              Depth                    :   25
%              Number of atoms          :  560 (5291 expanded)
%              Number of equality atoms :  234 (1278 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
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
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
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

fof(f39,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

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

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f8,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_644,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_628,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_642,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
    | r2_hidden(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_642])).

cnf(c_15,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_630,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_627,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_634,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1150,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_634])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_640,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1391,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1150,c_640])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_628])).

cnf(c_1513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1512,c_1391])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1518,plain,
    ( r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_24,c_25,c_26,c_27,c_28])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1518])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_638,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1885,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_638])).

cnf(c_2538,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_28])).

cnf(c_2539,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2538])).

cnf(c_2546,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_2539])).

cnf(c_4151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_2546])).

cnf(c_4152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4151,c_1391])).

cnf(c_4157,plain,
    ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4152,c_24,c_25,c_26,c_27,c_28,c_1519])).

cnf(c_4158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4157])).

cnf(c_4390,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_4158])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_643,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_643,c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_636,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2252,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_636])).

cnf(c_2711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2252,c_24,c_25,c_26,c_27,c_28])).

cnf(c_2712,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2711])).

cnf(c_2719,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_659,c_2712])).

cnf(c_4400,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4390,c_1391,c_2719])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2293,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_635])).

cnf(c_2367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2293,c_1391])).

cnf(c_2721,plain,
    ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2367,c_24,c_25,c_26,c_27,c_28])).

cnf(c_2722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2721])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_641])).

cnf(c_3094,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_2730])).

cnf(c_1527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_642])).

cnf(c_4166,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_4158])).

cnf(c_4167,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4166,c_2719])).

cnf(c_5055,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4400,c_3094,c_4167])).

cnf(c_5063,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5055,c_659])).

cnf(c_5067,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_644,c_5063])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6133,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5067,c_18])).

cnf(c_6134,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6133])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:42:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 24
% 3.73/0.98  conjectures                             6
% 3.73/0.98  EPR                                     7
% 3.73/0.98  Horn                                    13
% 3.73/0.98  unary                                   8
% 3.73/0.98  binary                                  3
% 3.73/0.98  lits                                    101
% 3.73/0.98  lits eq                                 7
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 1
% 3.73/0.98  fd_pseudo_cond                          1
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Input Options Time Limit: Unbounded
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98   Resolution empty clause
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f14,plain,(
% 3.73/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.73/0.98    inference(ennf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).
% 3.73/0.98  
% 3.73/0.98  fof(f40,plain,(
% 3.73/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.73/0.98    inference(cnf_transformation,[],[f30])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.73/0.98    inference(ennf_transformation,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.73/0.98    inference(flattening,[],[f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.73/0.98    inference(nnf_transformation,[],[f26])).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.73/0.98    inference(rectify,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 3.73/0.98  
% 3.73/0.98  fof(f52,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f4,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f15,plain,(
% 3.73/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f4])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,plain,(
% 3.73/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.73/0.98    inference(flattening,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  fof(f43,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f54,plain,(
% 3.73/0.98    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f12,conjecture,(
% 3.73/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f13,negated_conjecture,(
% 3.73/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.73/0.98    inference(negated_conjecture,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f27])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 3.73/0.98  
% 3.73/0.98  fof(f62,plain,(
% 3.73/0.98    l1_orders_2(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f10,axiom,(
% 3.73/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f24])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f18,plain,(
% 3.73/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f58,plain,(
% 3.73/0.98    ~v2_struct_0(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f59,plain,(
% 3.73/0.98    v3_orders_2(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f60,plain,(
% 3.73/0.98    v4_orders_2(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f61,plain,(
% 3.73/0.98    v5_orders_2(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(nnf_transformation,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.73/0.98    inference(flattening,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f47,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f32])).
% 3.73/0.98  
% 3.73/0.98  fof(f64,plain,(
% 3.73/0.98    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.73/0.98    inference(equality_resolution,[],[f47])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f41,plain,(
% 3.73/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.73/0.98    inference(cnf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f8,axiom,(
% 3.73/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f21,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f49,plain,(
% 3.73/0.98    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f21])).
% 3.73/0.98  
% 3.73/0.98  fof(f9,axiom,(
% 3.73/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f22,plain,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f22])).
% 3.73/0.98  
% 3.73/0.98  fof(f50,plain,(
% 3.73/0.98    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f17,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f44,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f63,plain,(
% 3.73/0.98    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_644,plain,
% 3.73/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_17,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.98      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.73/0.98      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.73/0.98      | v2_struct_0(X1)
% 3.73/0.98      | ~ v3_orders_2(X1)
% 3.73/0.98      | ~ v4_orders_2(X1)
% 3.73/0.98      | ~ v5_orders_2(X1)
% 3.73/0.98      | ~ l1_orders_2(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_628,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 3.73/0.98      | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
% 3.73/0.98      | v2_struct_0(X1) = iProver_top
% 3.73/0.98      | v3_orders_2(X1) != iProver_top
% 3.73/0.98      | v4_orders_2(X1) != iProver_top
% 3.73/0.98      | v5_orders_2(X1) != iProver_top
% 3.73/0.98      | l1_orders_2(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_642,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.73/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.73/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1359,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/0.98      | r2_hidden(X2,a_2_1_orders_2(X1,X0)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 3.73/0.98      | v2_struct_0(X1) = iProver_top
% 3.73/0.98      | v3_orders_2(X1) != iProver_top
% 3.73/0.98      | v4_orders_2(X1) != iProver_top
% 3.73/0.98      | v5_orders_2(X1) != iProver_top
% 3.73/0.98      | l1_orders_2(X1) != iProver_top
% 3.73/0.98      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_628,c_642]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_15,plain,
% 3.73/0.98      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.73/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.73/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.73/0.98      | ~ r2_hidden(X3,X2)
% 3.73/0.98      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.73/0.98      | v2_struct_0(X0)
% 3.73/0.98      | ~ v3_orders_2(X0)
% 3.73/0.98      | ~ v4_orders_2(X0)
% 3.73/0.98      | ~ v5_orders_2(X0)
% 3.73/0.98      | ~ l1_orders_2(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_630,plain,
% 3.73/0.98      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 3.73/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/0.98      | r2_hidden(X3,X2) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 3.73/0.98      | v2_struct_0(X0) = iProver_top
% 3.73/0.98      | v3_orders_2(X0) != iProver_top
% 3.73/0.98      | v4_orders_2(X0) != iProver_top
% 3.73/0.98      | v5_orders_2(X0) != iProver_top
% 3.73/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_19,negated_conjecture,
% 3.73/0.98      ( l1_orders_2(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_627,plain,
% 3.73/0.98      ( l1_orders_2(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_11,plain,
% 3.73/0.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_634,plain,
% 3.73/0.98      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1150,plain,
% 3.73/0.98      ( l1_struct_0(sK3) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_627,c_634]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5,plain,
% 3.73/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_640,plain,
% 3.73/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1391,plain,
% 3.73/0.98      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1150,c_640]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1512,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1391,c_628]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1513,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_1512,c_1391]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_24,plain,
% 3.73/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,negated_conjecture,
% 3.73/0.98      ( v3_orders_2(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_25,plain,
% 3.73/0.98      ( v3_orders_2(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_21,negated_conjecture,
% 3.73/0.98      ( v4_orders_2(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_26,plain,
% 3.73/0.98      ( v4_orders_2(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_20,negated_conjecture,
% 3.73/0.98      ( v5_orders_2(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_27,plain,
% 3.73/0.98      ( v5_orders_2(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_28,plain,
% 3.73/0.98      ( l1_orders_2(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1518,plain,
% 3.73/0.98      ( r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_1513,c_24,c_25,c_26,c_27,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1519,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_1518]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7,plain,
% 3.73/0.98      ( ~ r2_orders_2(X0,X1,X1)
% 3.73/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.73/0.98      | ~ l1_orders_2(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_638,plain,
% 3.73/0.98      ( r2_orders_2(X0,X1,X1) != iProver_top
% 3.73/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.73/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1885,plain,
% 3.73/0.98      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1391,c_638]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2538,plain,
% 3.73/0.98      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.73/0.98      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1885,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2539,plain,
% 3.73/0.98      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_2538]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2546,plain,
% 3.73/0.98      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 3.73/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1519,c_2539]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4151,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_630,c_2546]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4152,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_4151,c_1391]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4157,plain,
% 3.73/0.98      ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4152,c_24,c_25,c_26,c_27,c_28,c_1519]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4158,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_4157]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4390,plain,
% 3.73/0.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,a_2_1_orders_2(sK3,u1_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top
% 3.73/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1359,c_4158]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2,plain,
% 3.73/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_643,plain,
% 3.73/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1,plain,
% 3.73/0.98      ( k2_subset_1(X0) = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_659,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_643,c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.98      | v2_struct_0(X1)
% 3.73/0.98      | ~ v3_orders_2(X1)
% 3.73/0.98      | ~ v4_orders_2(X1)
% 3.73/0.98      | ~ v5_orders_2(X1)
% 3.73/0.98      | ~ l1_orders_2(X1)
% 3.73/0.98      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_636,plain,
% 3.73/0.98      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 3.73/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/0.98      | v2_struct_0(X0) = iProver_top
% 3.73/0.98      | v3_orders_2(X0) != iProver_top
% 3.73/0.98      | v4_orders_2(X0) != iProver_top
% 3.73/0.98      | v5_orders_2(X0) != iProver_top
% 3.73/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2252,plain,
% 3.73/0.98      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1391,c_636]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2711,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_2252,c_24,c_25,c_26,c_27,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2712,plain,
% 3.73/0.98      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_2711]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2719,plain,
% 3.73/0.98      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_659,c_2712]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4400,plain,
% 3.73/0.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_4390,c_1391,c_2719]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.98      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/0.98      | v2_struct_0(X1)
% 3.73/0.98      | ~ v3_orders_2(X1)
% 3.73/0.98      | ~ v4_orders_2(X1)
% 3.73/0.98      | ~ v5_orders_2(X1)
% 3.73/0.98      | ~ l1_orders_2(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_635,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/0.98      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.73/0.98      | v2_struct_0(X1) = iProver_top
% 3.73/0.98      | v3_orders_2(X1) != iProver_top
% 3.73/0.98      | v4_orders_2(X1) != iProver_top
% 3.73/0.98      | v5_orders_2(X1) != iProver_top
% 3.73/0.98      | l1_orders_2(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2293,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1391,c_635]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2367,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v3_orders_2(sK3) != iProver_top
% 3.73/0.98      | v4_orders_2(sK3) != iProver_top
% 3.73/0.98      | v5_orders_2(sK3) != iProver_top
% 3.73/0.98      | l1_orders_2(sK3) != iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_2293,c_1391]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2721,plain,
% 3.73/0.98      ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_2367,c_24,c_25,c_26,c_27,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2722,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_2721]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(X2,X0)
% 3.73/0.98      | ~ v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_641,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.73/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2730,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2722,c_641]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3094,plain,
% 3.73/0.98      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_659,c_2730]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1527,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1519,c_642]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4166,plain,
% 3.73/0.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1527,c_4158]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4167,plain,
% 3.73/0.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_4166,c_2719]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5055,plain,
% 3.73/0.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.73/0.98      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4400,c_3094,c_4167]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5063,plain,
% 3.73/0.98      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5055,c_659]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5067,plain,
% 3.73/0.98      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_644,c_5063]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18,negated_conjecture,
% 3.73/0.98      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6133,plain,
% 3.73/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_5067,c_18]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6134,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(equality_resolution_simp,[status(thm)],[c_6133]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ Selected
% 3.73/0.98  
% 3.73/0.98  total_time:                             0.331
% 3.73/0.98  
%------------------------------------------------------------------------------
