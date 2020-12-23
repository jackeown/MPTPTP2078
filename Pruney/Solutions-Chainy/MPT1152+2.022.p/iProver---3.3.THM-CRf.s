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
% DateTime   : Thu Dec  3 12:12:14 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 563 expanded)
%              Number of clauses        :   66 ( 160 expanded)
%              Number of leaves         :   16 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          :  544 (2680 expanded)
%              Number of equality atoms :  117 ( 482 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X1)
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,
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

fof(f43,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).

fof(f65,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f23,plain,(
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

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1150,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_23,c_22,c_21,c_19])).

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_292,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_4])).

cnf(c_620,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_292,c_19])).

cnf(c_621,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1147,c_621])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1153,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1153])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_407,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_408,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_23,c_22,c_21,c_19])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_428,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_412,c_1])).

cnf(c_1149,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1230,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1149,c_621])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_632,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_633,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1140,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1165,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_621])).

cnf(c_1914,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1165])).

cnf(c_4734,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1914,c_1205])).

cnf(c_4743,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_4734])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_281,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_625,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_281,c_19])).

cnf(c_626,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_1141,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1158,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1141,c_621])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_23,c_22,c_21,c_19])).

cnf(c_1142,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_1170,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1142,c_621])).

cnf(c_1351,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1158,c_1170])).

cnf(c_4744,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4743,c_1351])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_23,c_22,c_21,c_19])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1143,c_621])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1151])).

cnf(c_2555,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1659])).

cnf(c_5988,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4744,c_1158,c_2555])).

cnf(c_5995,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1150,c_5988])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6031,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5995,c_18])).

cnf(c_6032,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6031])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.53/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.00  
% 3.53/1.00  ------  iProver source info
% 3.53/1.00  
% 3.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.00  git: non_committed_changes: false
% 3.53/1.00  git: last_make_outside_of_git: false
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    --mode clausify
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         false
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     num_symb
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       true
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     false
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   []
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_full_bw                           [BwDemod]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  ------ Parsing...
% 3.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.00  ------ Proving...
% 3.53/1.00  ------ Problem Properties 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  clauses                                 16
% 3.53/1.00  conjectures                             1
% 3.53/1.00  EPR                                     1
% 3.53/1.00  Horn                                    12
% 3.53/1.00  unary                                   3
% 3.53/1.00  binary                                  4
% 3.53/1.00  lits                                    42
% 3.53/1.00  lits eq                                 5
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 1
% 3.53/1.00  fd_pseudo_cond                          0
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Schedule dynamic 5 is on 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    --mode clausify
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         false
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     none
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       false
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     false
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   []
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_full_bw                           [BwDemod]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00   Resolution empty clause
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0] : ~(! [X1] : ~(! [X2] : (r2_hidden(X2,X1) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f14,plain,(
% 3.53/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.53/1.00    inference(pure_predicate_removal,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f20,plain,(
% 3.53/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.53/1.00    inference(ennf_transformation,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f33,plain,(
% 3.53/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f34,plain,(
% 3.53/1.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).
% 3.53/1.00  
% 3.53/1.00  fof(f47,plain,(
% 3.53/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f34])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f29,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.53/1.00    inference(ennf_transformation,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f30,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.53/1.00    inference(flattening,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.53/1.00    inference(nnf_transformation,[],[f30])).
% 3.53/1.00  
% 3.53/1.00  fof(f38,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.53/1.00    inference(rectify,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f40,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f56,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f41])).
% 3.53/1.00  
% 3.53/1.00  fof(f12,conjecture,(
% 3.53/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f13,negated_conjecture,(
% 3.53/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.53/1.00    inference(negated_conjecture,[],[f12])).
% 3.53/1.00  
% 3.53/1.00  fof(f31,plain,(
% 3.53/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f13])).
% 3.53/1.00  
% 3.53/1.00  fof(f32,plain,(
% 3.53/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f31])).
% 3.53/1.00  
% 3.53/1.00  fof(f42,plain,(
% 3.53/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).
% 3.53/1.00  
% 3.53/1.00  fof(f65,plain,(
% 3.53/1.00    v5_orders_2(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ~v2_struct_0(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f63,plain,(
% 3.53/1.00    v3_orders_2(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f64,plain,(
% 3.53/1.00    v4_orders_2(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f66,plain,(
% 3.53/1.00    l1_orders_2(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f28,plain,(
% 3.53/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  fof(f55,plain,(
% 3.53/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f28])).
% 3.53/1.00  
% 3.53/1.00  fof(f5,axiom,(
% 3.53/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f21,plain,(
% 3.53/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f5])).
% 3.53/1.00  
% 3.53/1.00  fof(f48,plain,(
% 3.53/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f15,plain,(
% 3.53/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f16,plain,(
% 3.53/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.53/1.00    inference(flattening,[],[f15])).
% 3.53/1.00  
% 3.53/1.00  fof(f44,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f41])).
% 3.53/1.00  
% 3.53/1.00  fof(f2,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f17,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.53/1.00    inference(ennf_transformation,[],[f2])).
% 3.53/1.00  
% 3.53/1.00  fof(f18,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.53/1.00    inference(flattening,[],[f17])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f18])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f35,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.53/1.00    inference(flattening,[],[f35])).
% 3.53/1.00  
% 3.53/1.00  fof(f51,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f68,plain,(
% 3.53/1.00    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f51])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f22,plain,(
% 3.53/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f49,plain,(
% 3.53/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f8,axiom,(
% 3.53/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f24,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f8])).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f24])).
% 3.53/1.00  
% 3.53/1.00  fof(f53,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  fof(f9,axiom,(
% 3.53/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f9])).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f54,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f27])).
% 3.53/1.00  
% 3.53/1.00  fof(f3,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f19,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f3])).
% 3.53/1.00  
% 3.53/1.00  fof(f46,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f19])).
% 3.53/1.00  
% 3.53/1.00  fof(f67,plain,(
% 3.53/1.00    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1150,plain,
% 3.53/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.53/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ v5_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,negated_conjecture,
% 3.53/1.00      ( v5_orders_2(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_460,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 3.53/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1)
% 3.53/1.00      | sK3 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_461,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 3.53/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 3.53/1.00      | v2_struct_0(sK3)
% 3.53/1.00      | ~ v3_orders_2(sK3)
% 3.53/1.00      | ~ v4_orders_2(sK3)
% 3.53/1.00      | ~ l1_orders_2(sK3) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_23,negated_conjecture,
% 3.53/1.00      ( ~ v2_struct_0(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_22,negated_conjecture,
% 3.53/1.00      ( v3_orders_2(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_21,negated_conjecture,
% 3.53/1.00      ( v4_orders_2(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,negated_conjecture,
% 3.53/1.00      ( l1_orders_2(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_465,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 3.53/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_461,c_23,c_22,c_21,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1147,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 3.53/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11,plain,
% 3.53/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_292,plain,
% 3.53/1.00      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.53/1.00      inference(resolution,[status(thm)],[c_11,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_620,plain,
% 3.53/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_292,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_621,plain,
% 3.53/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_620]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1205,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.53/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1147,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1153,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.53/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1561,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.53/1.00      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1205,c_1153]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15,plain,
% 3.53/1.00      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.53/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.53/1.00      | ~ r2_hidden(X3,X2)
% 3.53/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.53/1.00      | v2_struct_0(X0)
% 3.53/1.00      | ~ v3_orders_2(X0)
% 3.53/1.00      | ~ v4_orders_2(X0)
% 3.53/1.00      | ~ v5_orders_2(X0)
% 3.53/1.00      | ~ l1_orders_2(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_407,plain,
% 3.53/1.00      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.53/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.53/1.00      | ~ r2_hidden(X3,X2)
% 3.53/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.53/1.00      | v2_struct_0(X0)
% 3.53/1.00      | ~ v3_orders_2(X0)
% 3.53/1.00      | ~ v4_orders_2(X0)
% 3.53/1.00      | ~ l1_orders_2(X0)
% 3.53/1.00      | sK3 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_408,plain,
% 3.53/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | ~ r2_hidden(X2,X1)
% 3.53/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.53/1.00      | v2_struct_0(sK3)
% 3.53/1.00      | ~ v3_orders_2(sK3)
% 3.53/1.00      | ~ v4_orders_2(sK3)
% 3.53/1.00      | ~ l1_orders_2(sK3) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_412,plain,
% 3.53/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | ~ r2_hidden(X2,X1)
% 3.53/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_408,c_23,c_22,c_21,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1)
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.53/1.00      | ~ r2_hidden(X0,X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_428,plain,
% 3.53/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | ~ r2_hidden(X2,X1)
% 3.53/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 3.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_412,c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1149,plain,
% 3.53/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1230,plain,
% 3.53/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1149,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7,plain,
% 3.53/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 3.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.53/1.00      | ~ l1_orders_2(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_632,plain,
% 3.53/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 3.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.53/1.00      | sK3 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_633,plain,
% 3.53/1.00      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_632]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1140,plain,
% 3.53/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1165,plain,
% 3.53/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1140,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1914,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 3.53/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.53/1.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1230,c_1165]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4734,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 3.53/1.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1914,c_1205]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4743,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1561,c_4734]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.53/1.00      | ~ l1_struct_0(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_281,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.53/1.00      | ~ l1_orders_2(X0) ),
% 3.53/1.00      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_625,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK3 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_281,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_626,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_625]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1141,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1158,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1141,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ v5_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1)
% 3.53/1.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_568,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1)
% 3.53/1.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 3.53/1.00      | sK3 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_569,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | v2_struct_0(sK3)
% 3.53/1.00      | ~ v3_orders_2(sK3)
% 3.53/1.00      | ~ v4_orders_2(sK3)
% 3.53/1.00      | ~ l1_orders_2(sK3)
% 3.53/1.00      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_568]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_573,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_569,c_23,c_22,c_21,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1142,plain,
% 3.53/1.00      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1170,plain,
% 3.53/1.00      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1142,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1351,plain,
% 3.53/1.00      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1158,c_1170]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4744,plain,
% 3.53/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_4743,c_1351]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ v5_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_550,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | ~ v3_orders_2(X1)
% 3.53/1.00      | ~ v4_orders_2(X1)
% 3.53/1.00      | ~ l1_orders_2(X1)
% 3.53/1.00      | sK3 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_551,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | v2_struct_0(sK3)
% 3.53/1.00      | ~ v3_orders_2(sK3)
% 3.53/1.00      | ~ v4_orders_2(sK3)
% 3.53/1.00      | ~ l1_orders_2(sK3) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_550]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_555,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.53/1.00      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_551,c_23,c_22,c_21,c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1143,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1181,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1143,c_621]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/1.00      | ~ r2_hidden(X2,X0)
% 3.53/1.00      | ~ v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1151,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.53/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.53/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1659,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1181,c_1151]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2555,plain,
% 3.53/1.00      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1158,c_1659]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5988,plain,
% 3.53/1.00      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4744,c_1158,c_2555]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5995,plain,
% 3.53/1.00      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1150,c_5988]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,negated_conjecture,
% 3.53/1.00      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6031,plain,
% 3.53/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_5995,c_18]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6032,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_6031]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.01
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.015
% 3.53/1.00  total_time:                             0.279
% 3.53/1.00  num_of_symbols:                         52
% 3.53/1.00  num_of_terms:                           6889
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    30
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       97
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        25
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        4
% 3.53/1.00  pred_elim:                              7
% 3.53/1.00  pred_elim_cl:                           8
% 3.53/1.00  pred_elim_cycles:                       12
% 3.53/1.00  merged_defs:                            0
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          0
% 3.53/1.00  prep_cycles:                            4
% 3.53/1.00  pred_elim_time:                         0.011
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                16
% 3.53/1.00  conjectures:                            1
% 3.53/1.00  epr:                                    1
% 3.53/1.00  horn:                                   12
% 3.53/1.00  ground:                                 3
% 3.53/1.00  unary:                                  3
% 3.53/1.00  binary:                                 4
% 3.53/1.00  lits:                                   42
% 3.53/1.00  lits_eq:                                5
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                1
% 3.53/1.00  fd_pseudo_cond:                         0
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      28
% 3.53/1.00  prop_fast_solver_calls:                 969
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    2907
% 3.53/1.00  prop_preprocess_simplified:             6083
% 3.53/1.00  prop_fo_subsumed:                       43
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    828
% 3.53/1.00  inst_num_in_passive:                    164
% 3.53/1.00  inst_num_in_active:                     344
% 3.53/1.00  inst_num_in_unprocessed:                320
% 3.53/1.00  inst_num_of_loops:                      380
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          32
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      44
% 3.53/1.00  inst_num_of_non_proper_insts:           600
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       101
% 3.53/1.00  res_forward_subset_subsumed:            46
% 3.53/1.00  res_backward_subset_subsumed:           0
% 3.53/1.00  res_forward_subsumed:                   0
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     5
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       370
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      40
% 3.53/1.00  res_num_eq_res_simplified:              0
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     74
% 3.53/1.00  sup_num_in_active:                      53
% 3.53/1.00  sup_num_in_passive:                     21
% 3.53/1.00  sup_num_of_loops:                       75
% 3.53/1.00  sup_fw_superposition:                   83
% 3.53/1.00  sup_bw_superposition:                   25
% 3.53/1.00  sup_immediate_simplified:               25
% 3.53/1.00  sup_given_eliminated:                   1
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    9
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 3
% 3.53/1.00  sim_bw_subset_subsumed:                 6
% 3.53/1.00  sim_fw_subsumed:                        7
% 3.53/1.00  sim_bw_subsumed:                        0
% 3.53/1.00  sim_fw_subsumption_res:                 3
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      2
% 3.53/1.00  sim_eq_tautology_del:                   0
% 3.53/1.00  sim_eq_res_simp:                        0
% 3.53/1.00  sim_fw_demodulated:                     7
% 3.53/1.00  sim_bw_demodulated:                     18
% 3.53/1.00  sim_light_normalised:                   21
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------
