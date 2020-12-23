%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:13 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 985 expanded)
%              Number of clauses        :   89 ( 283 expanded)
%              Number of leaves         :   18 ( 212 expanded)
%              Depth                    :   20
%              Number of atoms          :  614 (4570 expanded)
%              Number of equality atoms :  157 ( 852 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,
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

fof(f44,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f43])).

fof(f69,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f34])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_875,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1346,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_17918,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_295,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_639,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_21])).

cnf(c_640,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1156,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_306,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_6])).

cnf(c_634,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_21])).

cnf(c_635,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_1178,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1156,c_635])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1166,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_25,c_24,c_23,c_21])).

cnf(c_1161,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1212,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1161,c_635])).

cnf(c_1629,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
    | a_2_1_orders_2(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1212])).

cnf(c_2512,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1178,c_1629])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_25,c_24,c_23,c_21])).

cnf(c_1157,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1190,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1157,c_635])).

cnf(c_1366,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1178,c_1190])).

cnf(c_2522,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2512,c_1366])).

cnf(c_2523,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2522,c_1366])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_50,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_68,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_1343,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_876,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1384,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1535,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2401,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
    | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_874,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2402,plain,
    ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_3978,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,k2_struct_0(X0)))
    | sK2(X1,sK3,k2_struct_0(X0)) = X1 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_5397,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3978])).

cnf(c_8178,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_21,c_20,c_50,c_68,c_1316,c_1343,c_2401,c_2402,c_5397])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_421,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_422,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_25,c_24,c_23,c_21])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_442,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_426,c_3])).

cnf(c_1164,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1244,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1164,c_635])).

cnf(c_9,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_646,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_647,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_1155,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_1185,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1155,c_635])).

cnf(c_1835,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1185])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_25,c_24,c_23,c_21])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1162,c_635])).

cnf(c_3482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_1219])).

cnf(c_8184,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8178,c_3482])).

cnf(c_8193,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8184,c_1366])).

cnf(c_3500,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_25,c_24,c_23,c_21])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1158,c_635])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1820,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(X1,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1169])).

cnf(c_3323,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1820])).

cnf(c_3351,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_3323])).

cnf(c_1344,plain,
    ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1343])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17918,c_8193,c_3500,c_3351,c_1344,c_1178,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.41/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.41/1.50  
% 7.41/1.50  ------  iProver source info
% 7.41/1.50  
% 7.41/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.41/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.41/1.50  git: non_committed_changes: false
% 7.41/1.50  git: last_make_outside_of_git: false
% 7.41/1.50  
% 7.41/1.50  ------ 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options
% 7.41/1.50  
% 7.41/1.50  --out_options                           all
% 7.41/1.50  --tptp_safe_out                         true
% 7.41/1.50  --problem_path                          ""
% 7.41/1.50  --include_path                          ""
% 7.41/1.50  --clausifier                            res/vclausify_rel
% 7.41/1.50  --clausifier_options                    --mode clausify
% 7.41/1.50  --stdin                                 false
% 7.41/1.50  --stats_out                             all
% 7.41/1.50  
% 7.41/1.50  ------ General Options
% 7.41/1.50  
% 7.41/1.50  --fof                                   false
% 7.41/1.50  --time_out_real                         305.
% 7.41/1.50  --time_out_virtual                      -1.
% 7.41/1.50  --symbol_type_check                     false
% 7.41/1.50  --clausify_out                          false
% 7.41/1.50  --sig_cnt_out                           false
% 7.41/1.50  --trig_cnt_out                          false
% 7.41/1.50  --trig_cnt_out_tolerance                1.
% 7.41/1.50  --trig_cnt_out_sk_spl                   false
% 7.41/1.50  --abstr_cl_out                          false
% 7.41/1.50  
% 7.41/1.50  ------ Global Options
% 7.41/1.50  
% 7.41/1.50  --schedule                              default
% 7.41/1.50  --add_important_lit                     false
% 7.41/1.50  --prop_solver_per_cl                    1000
% 7.41/1.50  --min_unsat_core                        false
% 7.41/1.50  --soft_assumptions                      false
% 7.41/1.50  --soft_lemma_size                       3
% 7.41/1.50  --prop_impl_unit_size                   0
% 7.41/1.50  --prop_impl_unit                        []
% 7.41/1.50  --share_sel_clauses                     true
% 7.41/1.50  --reset_solvers                         false
% 7.41/1.50  --bc_imp_inh                            [conj_cone]
% 7.41/1.50  --conj_cone_tolerance                   3.
% 7.41/1.50  --extra_neg_conj                        none
% 7.41/1.50  --large_theory_mode                     true
% 7.41/1.50  --prolific_symb_bound                   200
% 7.41/1.50  --lt_threshold                          2000
% 7.41/1.50  --clause_weak_htbl                      true
% 7.41/1.50  --gc_record_bc_elim                     false
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing Options
% 7.41/1.50  
% 7.41/1.50  --preprocessing_flag                    true
% 7.41/1.50  --time_out_prep_mult                    0.1
% 7.41/1.50  --splitting_mode                        input
% 7.41/1.50  --splitting_grd                         true
% 7.41/1.50  --splitting_cvd                         false
% 7.41/1.50  --splitting_cvd_svl                     false
% 7.41/1.50  --splitting_nvd                         32
% 7.41/1.50  --sub_typing                            true
% 7.41/1.50  --prep_gs_sim                           true
% 7.41/1.50  --prep_unflatten                        true
% 7.41/1.50  --prep_res_sim                          true
% 7.41/1.50  --prep_upred                            true
% 7.41/1.50  --prep_sem_filter                       exhaustive
% 7.41/1.50  --prep_sem_filter_out                   false
% 7.41/1.50  --pred_elim                             true
% 7.41/1.50  --res_sim_input                         true
% 7.41/1.50  --eq_ax_congr_red                       true
% 7.41/1.50  --pure_diseq_elim                       true
% 7.41/1.50  --brand_transform                       false
% 7.41/1.50  --non_eq_to_eq                          false
% 7.41/1.50  --prep_def_merge                        true
% 7.41/1.50  --prep_def_merge_prop_impl              false
% 7.41/1.50  --prep_def_merge_mbd                    true
% 7.41/1.50  --prep_def_merge_tr_red                 false
% 7.41/1.50  --prep_def_merge_tr_cl                  false
% 7.41/1.50  --smt_preprocessing                     true
% 7.41/1.50  --smt_ac_axioms                         fast
% 7.41/1.50  --preprocessed_out                      false
% 7.41/1.50  --preprocessed_stats                    false
% 7.41/1.50  
% 7.41/1.50  ------ Abstraction refinement Options
% 7.41/1.50  
% 7.41/1.50  --abstr_ref                             []
% 7.41/1.50  --abstr_ref_prep                        false
% 7.41/1.50  --abstr_ref_until_sat                   false
% 7.41/1.50  --abstr_ref_sig_restrict                funpre
% 7.41/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.50  --abstr_ref_under                       []
% 7.41/1.50  
% 7.41/1.50  ------ SAT Options
% 7.41/1.50  
% 7.41/1.50  --sat_mode                              false
% 7.41/1.50  --sat_fm_restart_options                ""
% 7.41/1.50  --sat_gr_def                            false
% 7.41/1.50  --sat_epr_types                         true
% 7.41/1.50  --sat_non_cyclic_types                  false
% 7.41/1.50  --sat_finite_models                     false
% 7.41/1.50  --sat_fm_lemmas                         false
% 7.41/1.50  --sat_fm_prep                           false
% 7.41/1.50  --sat_fm_uc_incr                        true
% 7.41/1.50  --sat_out_model                         small
% 7.41/1.50  --sat_out_clauses                       false
% 7.41/1.50  
% 7.41/1.50  ------ QBF Options
% 7.41/1.50  
% 7.41/1.50  --qbf_mode                              false
% 7.41/1.50  --qbf_elim_univ                         false
% 7.41/1.50  --qbf_dom_inst                          none
% 7.41/1.50  --qbf_dom_pre_inst                      false
% 7.41/1.50  --qbf_sk_in                             false
% 7.41/1.50  --qbf_pred_elim                         true
% 7.41/1.50  --qbf_split                             512
% 7.41/1.50  
% 7.41/1.50  ------ BMC1 Options
% 7.41/1.50  
% 7.41/1.50  --bmc1_incremental                      false
% 7.41/1.50  --bmc1_axioms                           reachable_all
% 7.41/1.50  --bmc1_min_bound                        0
% 7.41/1.50  --bmc1_max_bound                        -1
% 7.41/1.50  --bmc1_max_bound_default                -1
% 7.41/1.50  --bmc1_symbol_reachability              true
% 7.41/1.50  --bmc1_property_lemmas                  false
% 7.41/1.50  --bmc1_k_induction                      false
% 7.41/1.50  --bmc1_non_equiv_states                 false
% 7.41/1.50  --bmc1_deadlock                         false
% 7.41/1.50  --bmc1_ucm                              false
% 7.41/1.50  --bmc1_add_unsat_core                   none
% 7.41/1.50  --bmc1_unsat_core_children              false
% 7.41/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.50  --bmc1_out_stat                         full
% 7.41/1.50  --bmc1_ground_init                      false
% 7.41/1.50  --bmc1_pre_inst_next_state              false
% 7.41/1.50  --bmc1_pre_inst_state                   false
% 7.41/1.50  --bmc1_pre_inst_reach_state             false
% 7.41/1.50  --bmc1_out_unsat_core                   false
% 7.41/1.50  --bmc1_aig_witness_out                  false
% 7.41/1.50  --bmc1_verbose                          false
% 7.41/1.50  --bmc1_dump_clauses_tptp                false
% 7.41/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.50  --bmc1_dump_file                        -
% 7.41/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.50  --bmc1_ucm_extend_mode                  1
% 7.41/1.50  --bmc1_ucm_init_mode                    2
% 7.41/1.50  --bmc1_ucm_cone_mode                    none
% 7.41/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.50  --bmc1_ucm_relax_model                  4
% 7.41/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.50  --bmc1_ucm_layered_model                none
% 7.41/1.50  --bmc1_ucm_max_lemma_size               10
% 7.41/1.50  
% 7.41/1.50  ------ AIG Options
% 7.41/1.50  
% 7.41/1.50  --aig_mode                              false
% 7.41/1.50  
% 7.41/1.50  ------ Instantiation Options
% 7.41/1.50  
% 7.41/1.50  --instantiation_flag                    true
% 7.41/1.50  --inst_sos_flag                         false
% 7.41/1.50  --inst_sos_phase                        true
% 7.41/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel_side                     num_symb
% 7.41/1.50  --inst_solver_per_active                1400
% 7.41/1.50  --inst_solver_calls_frac                1.
% 7.41/1.50  --inst_passive_queue_type               priority_queues
% 7.41/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.50  --inst_passive_queues_freq              [25;2]
% 7.41/1.50  --inst_dismatching                      true
% 7.41/1.50  --inst_eager_unprocessed_to_passive     true
% 7.41/1.50  --inst_prop_sim_given                   true
% 7.41/1.50  --inst_prop_sim_new                     false
% 7.41/1.50  --inst_subs_new                         false
% 7.41/1.50  --inst_eq_res_simp                      false
% 7.41/1.50  --inst_subs_given                       false
% 7.41/1.50  --inst_orphan_elimination               true
% 7.41/1.50  --inst_learning_loop_flag               true
% 7.41/1.50  --inst_learning_start                   3000
% 7.41/1.50  --inst_learning_factor                  2
% 7.41/1.50  --inst_start_prop_sim_after_learn       3
% 7.41/1.50  --inst_sel_renew                        solver
% 7.41/1.50  --inst_lit_activity_flag                true
% 7.41/1.50  --inst_restr_to_given                   false
% 7.41/1.50  --inst_activity_threshold               500
% 7.41/1.50  --inst_out_proof                        true
% 7.41/1.50  
% 7.41/1.50  ------ Resolution Options
% 7.41/1.50  
% 7.41/1.50  --resolution_flag                       true
% 7.41/1.50  --res_lit_sel                           adaptive
% 7.41/1.50  --res_lit_sel_side                      none
% 7.41/1.50  --res_ordering                          kbo
% 7.41/1.50  --res_to_prop_solver                    active
% 7.41/1.50  --res_prop_simpl_new                    false
% 7.41/1.50  --res_prop_simpl_given                  true
% 7.41/1.50  --res_passive_queue_type                priority_queues
% 7.41/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.50  --res_passive_queues_freq               [15;5]
% 7.41/1.50  --res_forward_subs                      full
% 7.41/1.50  --res_backward_subs                     full
% 7.41/1.50  --res_forward_subs_resolution           true
% 7.41/1.50  --res_backward_subs_resolution          true
% 7.41/1.50  --res_orphan_elimination                true
% 7.41/1.50  --res_time_limit                        2.
% 7.41/1.50  --res_out_proof                         true
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Options
% 7.41/1.50  
% 7.41/1.50  --superposition_flag                    true
% 7.41/1.50  --sup_passive_queue_type                priority_queues
% 7.41/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.50  --demod_completeness_check              fast
% 7.41/1.50  --demod_use_ground                      true
% 7.41/1.50  --sup_to_prop_solver                    passive
% 7.41/1.50  --sup_prop_simpl_new                    true
% 7.41/1.50  --sup_prop_simpl_given                  true
% 7.41/1.50  --sup_fun_splitting                     false
% 7.41/1.50  --sup_smt_interval                      50000
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Simplification Setup
% 7.41/1.50  
% 7.41/1.50  --sup_indices_passive                   []
% 7.41/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_full_bw                           [BwDemod]
% 7.41/1.50  --sup_immed_triv                        [TrivRules]
% 7.41/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_immed_bw_main                     []
% 7.41/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  
% 7.41/1.50  ------ Combination Options
% 7.41/1.50  
% 7.41/1.50  --comb_res_mult                         3
% 7.41/1.50  --comb_sup_mult                         2
% 7.41/1.50  --comb_inst_mult                        10
% 7.41/1.50  
% 7.41/1.50  ------ Debug Options
% 7.41/1.50  
% 7.41/1.50  --dbg_backtrace                         false
% 7.41/1.50  --dbg_dump_prop_clauses                 false
% 7.41/1.50  --dbg_dump_prop_clauses_file            -
% 7.41/1.50  --dbg_out_stat                          false
% 7.41/1.50  ------ Parsing...
% 7.41/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.41/1.50  ------ Proving...
% 7.41/1.50  ------ Problem Properties 
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  clauses                                 17
% 7.41/1.50  conjectures                             1
% 7.41/1.50  EPR                                     1
% 7.41/1.50  Horn                                    14
% 7.41/1.50  unary                                   5
% 7.41/1.50  binary                                  4
% 7.41/1.50  lits                                    41
% 7.41/1.50  lits eq                                 5
% 7.41/1.50  fd_pure                                 0
% 7.41/1.50  fd_pseudo                               0
% 7.41/1.50  fd_cond                                 1
% 7.41/1.50  fd_pseudo_cond                          0
% 7.41/1.50  AC symbols                              0
% 7.41/1.50  
% 7.41/1.50  ------ Schedule dynamic 5 is on 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  ------ 
% 7.41/1.50  Current options:
% 7.41/1.50  ------ 
% 7.41/1.50  
% 7.41/1.50  ------ Input Options
% 7.41/1.50  
% 7.41/1.50  --out_options                           all
% 7.41/1.50  --tptp_safe_out                         true
% 7.41/1.50  --problem_path                          ""
% 7.41/1.50  --include_path                          ""
% 7.41/1.50  --clausifier                            res/vclausify_rel
% 7.41/1.50  --clausifier_options                    --mode clausify
% 7.41/1.50  --stdin                                 false
% 7.41/1.50  --stats_out                             all
% 7.41/1.50  
% 7.41/1.50  ------ General Options
% 7.41/1.50  
% 7.41/1.50  --fof                                   false
% 7.41/1.50  --time_out_real                         305.
% 7.41/1.50  --time_out_virtual                      -1.
% 7.41/1.50  --symbol_type_check                     false
% 7.41/1.50  --clausify_out                          false
% 7.41/1.50  --sig_cnt_out                           false
% 7.41/1.50  --trig_cnt_out                          false
% 7.41/1.50  --trig_cnt_out_tolerance                1.
% 7.41/1.50  --trig_cnt_out_sk_spl                   false
% 7.41/1.50  --abstr_cl_out                          false
% 7.41/1.50  
% 7.41/1.50  ------ Global Options
% 7.41/1.50  
% 7.41/1.50  --schedule                              default
% 7.41/1.50  --add_important_lit                     false
% 7.41/1.50  --prop_solver_per_cl                    1000
% 7.41/1.50  --min_unsat_core                        false
% 7.41/1.50  --soft_assumptions                      false
% 7.41/1.50  --soft_lemma_size                       3
% 7.41/1.50  --prop_impl_unit_size                   0
% 7.41/1.50  --prop_impl_unit                        []
% 7.41/1.50  --share_sel_clauses                     true
% 7.41/1.50  --reset_solvers                         false
% 7.41/1.50  --bc_imp_inh                            [conj_cone]
% 7.41/1.50  --conj_cone_tolerance                   3.
% 7.41/1.50  --extra_neg_conj                        none
% 7.41/1.50  --large_theory_mode                     true
% 7.41/1.50  --prolific_symb_bound                   200
% 7.41/1.50  --lt_threshold                          2000
% 7.41/1.50  --clause_weak_htbl                      true
% 7.41/1.50  --gc_record_bc_elim                     false
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing Options
% 7.41/1.50  
% 7.41/1.50  --preprocessing_flag                    true
% 7.41/1.50  --time_out_prep_mult                    0.1
% 7.41/1.50  --splitting_mode                        input
% 7.41/1.50  --splitting_grd                         true
% 7.41/1.50  --splitting_cvd                         false
% 7.41/1.50  --splitting_cvd_svl                     false
% 7.41/1.50  --splitting_nvd                         32
% 7.41/1.50  --sub_typing                            true
% 7.41/1.50  --prep_gs_sim                           true
% 7.41/1.50  --prep_unflatten                        true
% 7.41/1.50  --prep_res_sim                          true
% 7.41/1.50  --prep_upred                            true
% 7.41/1.50  --prep_sem_filter                       exhaustive
% 7.41/1.50  --prep_sem_filter_out                   false
% 7.41/1.50  --pred_elim                             true
% 7.41/1.50  --res_sim_input                         true
% 7.41/1.50  --eq_ax_congr_red                       true
% 7.41/1.50  --pure_diseq_elim                       true
% 7.41/1.50  --brand_transform                       false
% 7.41/1.50  --non_eq_to_eq                          false
% 7.41/1.50  --prep_def_merge                        true
% 7.41/1.50  --prep_def_merge_prop_impl              false
% 7.41/1.50  --prep_def_merge_mbd                    true
% 7.41/1.50  --prep_def_merge_tr_red                 false
% 7.41/1.50  --prep_def_merge_tr_cl                  false
% 7.41/1.50  --smt_preprocessing                     true
% 7.41/1.50  --smt_ac_axioms                         fast
% 7.41/1.50  --preprocessed_out                      false
% 7.41/1.50  --preprocessed_stats                    false
% 7.41/1.50  
% 7.41/1.50  ------ Abstraction refinement Options
% 7.41/1.50  
% 7.41/1.50  --abstr_ref                             []
% 7.41/1.50  --abstr_ref_prep                        false
% 7.41/1.50  --abstr_ref_until_sat                   false
% 7.41/1.50  --abstr_ref_sig_restrict                funpre
% 7.41/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.50  --abstr_ref_under                       []
% 7.41/1.50  
% 7.41/1.50  ------ SAT Options
% 7.41/1.50  
% 7.41/1.50  --sat_mode                              false
% 7.41/1.50  --sat_fm_restart_options                ""
% 7.41/1.50  --sat_gr_def                            false
% 7.41/1.50  --sat_epr_types                         true
% 7.41/1.50  --sat_non_cyclic_types                  false
% 7.41/1.50  --sat_finite_models                     false
% 7.41/1.50  --sat_fm_lemmas                         false
% 7.41/1.50  --sat_fm_prep                           false
% 7.41/1.50  --sat_fm_uc_incr                        true
% 7.41/1.50  --sat_out_model                         small
% 7.41/1.50  --sat_out_clauses                       false
% 7.41/1.50  
% 7.41/1.50  ------ QBF Options
% 7.41/1.50  
% 7.41/1.50  --qbf_mode                              false
% 7.41/1.50  --qbf_elim_univ                         false
% 7.41/1.50  --qbf_dom_inst                          none
% 7.41/1.50  --qbf_dom_pre_inst                      false
% 7.41/1.50  --qbf_sk_in                             false
% 7.41/1.50  --qbf_pred_elim                         true
% 7.41/1.50  --qbf_split                             512
% 7.41/1.50  
% 7.41/1.50  ------ BMC1 Options
% 7.41/1.50  
% 7.41/1.50  --bmc1_incremental                      false
% 7.41/1.50  --bmc1_axioms                           reachable_all
% 7.41/1.50  --bmc1_min_bound                        0
% 7.41/1.50  --bmc1_max_bound                        -1
% 7.41/1.50  --bmc1_max_bound_default                -1
% 7.41/1.50  --bmc1_symbol_reachability              true
% 7.41/1.50  --bmc1_property_lemmas                  false
% 7.41/1.50  --bmc1_k_induction                      false
% 7.41/1.50  --bmc1_non_equiv_states                 false
% 7.41/1.50  --bmc1_deadlock                         false
% 7.41/1.50  --bmc1_ucm                              false
% 7.41/1.50  --bmc1_add_unsat_core                   none
% 7.41/1.50  --bmc1_unsat_core_children              false
% 7.41/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.50  --bmc1_out_stat                         full
% 7.41/1.50  --bmc1_ground_init                      false
% 7.41/1.50  --bmc1_pre_inst_next_state              false
% 7.41/1.50  --bmc1_pre_inst_state                   false
% 7.41/1.50  --bmc1_pre_inst_reach_state             false
% 7.41/1.50  --bmc1_out_unsat_core                   false
% 7.41/1.50  --bmc1_aig_witness_out                  false
% 7.41/1.50  --bmc1_verbose                          false
% 7.41/1.50  --bmc1_dump_clauses_tptp                false
% 7.41/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.50  --bmc1_dump_file                        -
% 7.41/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.50  --bmc1_ucm_extend_mode                  1
% 7.41/1.50  --bmc1_ucm_init_mode                    2
% 7.41/1.50  --bmc1_ucm_cone_mode                    none
% 7.41/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.50  --bmc1_ucm_relax_model                  4
% 7.41/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.50  --bmc1_ucm_layered_model                none
% 7.41/1.50  --bmc1_ucm_max_lemma_size               10
% 7.41/1.50  
% 7.41/1.50  ------ AIG Options
% 7.41/1.50  
% 7.41/1.50  --aig_mode                              false
% 7.41/1.50  
% 7.41/1.50  ------ Instantiation Options
% 7.41/1.50  
% 7.41/1.50  --instantiation_flag                    true
% 7.41/1.50  --inst_sos_flag                         false
% 7.41/1.50  --inst_sos_phase                        true
% 7.41/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.50  --inst_lit_sel_side                     none
% 7.41/1.50  --inst_solver_per_active                1400
% 7.41/1.50  --inst_solver_calls_frac                1.
% 7.41/1.50  --inst_passive_queue_type               priority_queues
% 7.41/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.50  --inst_passive_queues_freq              [25;2]
% 7.41/1.50  --inst_dismatching                      true
% 7.41/1.50  --inst_eager_unprocessed_to_passive     true
% 7.41/1.50  --inst_prop_sim_given                   true
% 7.41/1.50  --inst_prop_sim_new                     false
% 7.41/1.50  --inst_subs_new                         false
% 7.41/1.50  --inst_eq_res_simp                      false
% 7.41/1.50  --inst_subs_given                       false
% 7.41/1.50  --inst_orphan_elimination               true
% 7.41/1.50  --inst_learning_loop_flag               true
% 7.41/1.50  --inst_learning_start                   3000
% 7.41/1.50  --inst_learning_factor                  2
% 7.41/1.50  --inst_start_prop_sim_after_learn       3
% 7.41/1.50  --inst_sel_renew                        solver
% 7.41/1.50  --inst_lit_activity_flag                true
% 7.41/1.50  --inst_restr_to_given                   false
% 7.41/1.50  --inst_activity_threshold               500
% 7.41/1.50  --inst_out_proof                        true
% 7.41/1.50  
% 7.41/1.50  ------ Resolution Options
% 7.41/1.50  
% 7.41/1.50  --resolution_flag                       false
% 7.41/1.50  --res_lit_sel                           adaptive
% 7.41/1.50  --res_lit_sel_side                      none
% 7.41/1.50  --res_ordering                          kbo
% 7.41/1.50  --res_to_prop_solver                    active
% 7.41/1.50  --res_prop_simpl_new                    false
% 7.41/1.50  --res_prop_simpl_given                  true
% 7.41/1.50  --res_passive_queue_type                priority_queues
% 7.41/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.50  --res_passive_queues_freq               [15;5]
% 7.41/1.50  --res_forward_subs                      full
% 7.41/1.50  --res_backward_subs                     full
% 7.41/1.50  --res_forward_subs_resolution           true
% 7.41/1.50  --res_backward_subs_resolution          true
% 7.41/1.50  --res_orphan_elimination                true
% 7.41/1.50  --res_time_limit                        2.
% 7.41/1.50  --res_out_proof                         true
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Options
% 7.41/1.50  
% 7.41/1.50  --superposition_flag                    true
% 7.41/1.50  --sup_passive_queue_type                priority_queues
% 7.41/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.50  --demod_completeness_check              fast
% 7.41/1.50  --demod_use_ground                      true
% 7.41/1.50  --sup_to_prop_solver                    passive
% 7.41/1.50  --sup_prop_simpl_new                    true
% 7.41/1.50  --sup_prop_simpl_given                  true
% 7.41/1.50  --sup_fun_splitting                     false
% 7.41/1.50  --sup_smt_interval                      50000
% 7.41/1.50  
% 7.41/1.50  ------ Superposition Simplification Setup
% 7.41/1.50  
% 7.41/1.50  --sup_indices_passive                   []
% 7.41/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_full_bw                           [BwDemod]
% 7.41/1.50  --sup_immed_triv                        [TrivRules]
% 7.41/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_immed_bw_main                     []
% 7.41/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.41/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.41/1.50  
% 7.41/1.50  ------ Combination Options
% 7.41/1.50  
% 7.41/1.50  --comb_res_mult                         3
% 7.41/1.50  --comb_sup_mult                         2
% 7.41/1.50  --comb_inst_mult                        10
% 7.41/1.50  
% 7.41/1.50  ------ Debug Options
% 7.41/1.50  
% 7.41/1.50  --dbg_backtrace                         false
% 7.41/1.50  --dbg_dump_prop_clauses                 false
% 7.41/1.50  --dbg_dump_prop_clauses_file            -
% 7.41/1.50  --dbg_out_stat                          false
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  ------ Proving...
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  % SZS status Theorem for theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  fof(f12,axiom,(
% 7.41/1.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f29,plain,(
% 7.41/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f12])).
% 7.41/1.50  
% 7.41/1.50  fof(f58,plain,(
% 7.41/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f29])).
% 7.41/1.50  
% 7.41/1.50  fof(f8,axiom,(
% 7.41/1.50    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f23,plain,(
% 7.41/1.50    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f8])).
% 7.41/1.50  
% 7.41/1.50  fof(f52,plain,(
% 7.41/1.50    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f23])).
% 7.41/1.50  
% 7.41/1.50  fof(f14,conjecture,(
% 7.41/1.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f15,negated_conjecture,(
% 7.41/1.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 7.41/1.50    inference(negated_conjecture,[],[f14])).
% 7.41/1.50  
% 7.41/1.50  fof(f32,plain,(
% 7.41/1.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f15])).
% 7.41/1.50  
% 7.41/1.50  fof(f33,plain,(
% 7.41/1.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f32])).
% 7.41/1.50  
% 7.41/1.50  fof(f43,plain,(
% 7.41/1.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f44,plain,(
% 7.41/1.50    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 7.41/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f43])).
% 7.41/1.50  
% 7.41/1.50  fof(f69,plain,(
% 7.41/1.50    l1_orders_2(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f7,axiom,(
% 7.41/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f22,plain,(
% 7.41/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f7])).
% 7.41/1.50  
% 7.41/1.50  fof(f51,plain,(
% 7.41/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f22])).
% 7.41/1.50  
% 7.41/1.50  fof(f6,axiom,(
% 7.41/1.50    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f16,plain,(
% 7.41/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.41/1.50    inference(pure_predicate_removal,[],[f6])).
% 7.41/1.50  
% 7.41/1.50  fof(f21,plain,(
% 7.41/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.41/1.50    inference(ennf_transformation,[],[f16])).
% 7.41/1.50  
% 7.41/1.50  fof(f34,plain,(
% 7.41/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f35,plain,(
% 7.41/1.50    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 7.41/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f34])).
% 7.41/1.50  
% 7.41/1.50  fof(f50,plain,(
% 7.41/1.50    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 7.41/1.50    inference(cnf_transformation,[],[f35])).
% 7.41/1.50  
% 7.41/1.50  fof(f13,axiom,(
% 7.41/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f30,plain,(
% 7.41/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 7.41/1.50    inference(ennf_transformation,[],[f13])).
% 7.41/1.50  
% 7.41/1.50  fof(f31,plain,(
% 7.41/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.41/1.50    inference(flattening,[],[f30])).
% 7.41/1.50  
% 7.41/1.50  fof(f38,plain,(
% 7.41/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.41/1.50    inference(nnf_transformation,[],[f31])).
% 7.41/1.50  
% 7.41/1.50  fof(f39,plain,(
% 7.41/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.41/1.50    inference(rectify,[],[f38])).
% 7.41/1.50  
% 7.41/1.50  fof(f41,plain,(
% 7.41/1.50    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f40,plain,(
% 7.41/1.50    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 7.41/1.50    introduced(choice_axiom,[])).
% 7.41/1.50  
% 7.41/1.50  fof(f42,plain,(
% 7.41/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.41/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 7.41/1.50  
% 7.41/1.50  fof(f60,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f42])).
% 7.41/1.50  
% 7.41/1.50  fof(f68,plain,(
% 7.41/1.50    v5_orders_2(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f65,plain,(
% 7.41/1.50    ~v2_struct_0(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f66,plain,(
% 7.41/1.50    v3_orders_2(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f67,plain,(
% 7.41/1.50    v4_orders_2(sK3)),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f10,axiom,(
% 7.41/1.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f25,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f10])).
% 7.41/1.50  
% 7.41/1.50  fof(f26,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f25])).
% 7.41/1.50  
% 7.41/1.50  fof(f56,plain,(
% 7.41/1.50    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f26])).
% 7.41/1.50  
% 7.41/1.50  fof(f70,plain,(
% 7.41/1.50    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 7.41/1.50    inference(cnf_transformation,[],[f44])).
% 7.41/1.50  
% 7.41/1.50  fof(f61,plain,(
% 7.41/1.50    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f42])).
% 7.41/1.50  
% 7.41/1.50  fof(f4,axiom,(
% 7.41/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f18,plain,(
% 7.41/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.41/1.50    inference(ennf_transformation,[],[f4])).
% 7.41/1.50  
% 7.41/1.50  fof(f19,plain,(
% 7.41/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.41/1.50    inference(flattening,[],[f18])).
% 7.41/1.50  
% 7.41/1.50  fof(f48,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f19])).
% 7.41/1.50  
% 7.41/1.50  fof(f9,axiom,(
% 7.41/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f24,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.50    inference(ennf_transformation,[],[f9])).
% 7.41/1.50  
% 7.41/1.50  fof(f36,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.50    inference(nnf_transformation,[],[f24])).
% 7.41/1.50  
% 7.41/1.50  fof(f37,plain,(
% 7.41/1.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.41/1.50    inference(flattening,[],[f36])).
% 7.41/1.50  
% 7.41/1.50  fof(f54,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f37])).
% 7.41/1.50  
% 7.41/1.50  fof(f71,plain,(
% 7.41/1.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.41/1.50    inference(equality_resolution,[],[f54])).
% 7.41/1.50  
% 7.41/1.50  fof(f59,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f42])).
% 7.41/1.50  
% 7.41/1.50  fof(f11,axiom,(
% 7.41/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f27,plain,(
% 7.41/1.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f11])).
% 7.41/1.50  
% 7.41/1.50  fof(f28,plain,(
% 7.41/1.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.41/1.50    inference(flattening,[],[f27])).
% 7.41/1.50  
% 7.41/1.50  fof(f57,plain,(
% 7.41/1.50    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.41/1.50    inference(cnf_transformation,[],[f28])).
% 7.41/1.50  
% 7.41/1.50  fof(f2,axiom,(
% 7.41/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.41/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.41/1.50  
% 7.41/1.50  fof(f17,plain,(
% 7.41/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.41/1.50    inference(ennf_transformation,[],[f2])).
% 7.41/1.50  
% 7.41/1.50  fof(f46,plain,(
% 7.41/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.41/1.50    inference(cnf_transformation,[],[f17])).
% 7.41/1.50  
% 7.41/1.50  cnf(c_875,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1346,plain,
% 7.41/1.50      ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
% 7.41/1.50      | k1_xboole_0 != X0
% 7.41/1.50      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_875]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_17918,plain,
% 7.41/1.50      ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 7.41/1.50      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 7.41/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_1346]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_13,plain,
% 7.41/1.50      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_7,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.50      | ~ l1_struct_0(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_295,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.50      | ~ l1_orders_2(X0) ),
% 7.41/1.50      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_21,negated_conjecture,
% 7.41/1.50      ( l1_orders_2(sK3) ),
% 7.41/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_639,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.50      | sK3 != X0 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_295,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_640,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_639]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1156,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_6,plain,
% 7.41/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_306,plain,
% 7.41/1.50      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.41/1.50      inference(resolution,[status(thm)],[c_13,c_6]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_634,plain,
% 7.41/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_306,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_635,plain,
% 7.41/1.50      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_634]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1178,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1156,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_5,plain,
% 7.41/1.50      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 7.41/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1166,plain,
% 7.41/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_18,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ v5_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | sK2(X2,X1,X0) = X2 ),
% 7.41/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_22,negated_conjecture,
% 7.41/1.50      ( v5_orders_2(sK3) ),
% 7.41/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_495,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | sK2(X2,X1,X0) = X2
% 7.41/1.50      | sK3 != X1 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_496,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 7.41/1.50      | v2_struct_0(sK3)
% 7.41/1.50      | ~ v3_orders_2(sK3)
% 7.41/1.50      | ~ v4_orders_2(sK3)
% 7.41/1.50      | ~ l1_orders_2(sK3)
% 7.41/1.50      | sK2(X1,sK3,X0) = X1 ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_495]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_25,negated_conjecture,
% 7.41/1.50      ( ~ v2_struct_0(sK3) ),
% 7.41/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_24,negated_conjecture,
% 7.41/1.50      ( v3_orders_2(sK3) ),
% 7.41/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_23,negated_conjecture,
% 7.41/1.50      ( v4_orders_2(sK3) ),
% 7.41/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_500,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 7.41/1.50      | sK2(X1,sK3,X0) = X1 ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_496,c_25,c_24,c_23,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1161,plain,
% 7.41/1.50      ( sK2(X0,sK3,X1) = X0
% 7.41/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1212,plain,
% 7.41/1.50      ( sK2(X0,sK3,X1) = X0
% 7.41/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1161,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1629,plain,
% 7.41/1.50      ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
% 7.41/1.50      | a_2_1_orders_2(sK3,X0) = k1_xboole_0
% 7.41/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1166,c_1212]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2512,plain,
% 7.41/1.50      ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1178,c_1629]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_11,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ v5_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_582,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 7.41/1.50      | sK3 != X1 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_583,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | v2_struct_0(sK3)
% 7.41/1.50      | ~ v3_orders_2(sK3)
% 7.41/1.50      | ~ v4_orders_2(sK3)
% 7.41/1.50      | ~ l1_orders_2(sK3)
% 7.41/1.50      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_582]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_587,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_583,c_25,c_24,c_23,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1157,plain,
% 7.41/1.50      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 7.41/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1190,plain,
% 7.41/1.50      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 7.41/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1157,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1366,plain,
% 7.41/1.50      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1178,c_1190]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2522,plain,
% 7.41/1.50      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_2512,c_1366]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2523,plain,
% 7.41/1.50      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 7.41/1.50      inference(demodulation,[status(thm)],[c_2522,c_1366]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_20,negated_conjecture,
% 7.41/1.50      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_50,plain,
% 7.41/1.50      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_68,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ l1_struct_0(sK3) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1316,plain,
% 7.41/1.50      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_587]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1343,plain,
% 7.41/1.50      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_876,plain,
% 7.41/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.41/1.50      theory(equality) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1384,plain,
% 7.41/1.50      ( r2_hidden(X0,X1)
% 7.41/1.50      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
% 7.41/1.50      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_876]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1535,plain,
% 7.41/1.50      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_1384]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2401,plain,
% 7.41/1.50      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
% 7.41/1.50      | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_1535]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_874,plain,( X0 = X0 ),theory(equality) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_2402,plain,
% 7.41/1.50      ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_874]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3978,plain,
% 7.41/1.50      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,k2_struct_0(X0)))
% 7.41/1.50      | sK2(X1,sK3,k2_struct_0(X0)) = X1 ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_500]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_5397,plain,
% 7.41/1.50      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 7.41/1.50      | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_3978]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_8178,plain,
% 7.41/1.50      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_2523,c_21,c_20,c_50,c_68,c_1316,c_1343,c_2401,c_2402,
% 7.41/1.50                 c_5397]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_17,plain,
% 7.41/1.50      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 7.41/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.41/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.50      | ~ r2_hidden(X3,X2)
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 7.41/1.50      | v2_struct_0(X0)
% 7.41/1.50      | ~ v3_orders_2(X0)
% 7.41/1.50      | ~ v4_orders_2(X0)
% 7.41/1.50      | ~ v5_orders_2(X0)
% 7.41/1.50      | ~ l1_orders_2(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_421,plain,
% 7.41/1.50      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 7.41/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.41/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.41/1.50      | ~ r2_hidden(X3,X2)
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 7.41/1.50      | v2_struct_0(X0)
% 7.41/1.50      | ~ v3_orders_2(X0)
% 7.41/1.50      | ~ v4_orders_2(X0)
% 7.41/1.50      | ~ l1_orders_2(X0)
% 7.41/1.50      | sK3 != X0 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_422,plain,
% 7.41/1.50      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 7.41/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 7.41/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X2,X1)
% 7.41/1.50      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 7.41/1.50      | v2_struct_0(sK3)
% 7.41/1.50      | ~ v3_orders_2(sK3)
% 7.41/1.50      | ~ v4_orders_2(sK3)
% 7.41/1.50      | ~ l1_orders_2(sK3) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_421]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_426,plain,
% 7.41/1.50      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 7.41/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 7.41/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X2,X1)
% 7.41/1.50      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_422,c_25,c_24,c_23,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3,plain,
% 7.41/1.50      ( m1_subset_1(X0,X1)
% 7.41/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.41/1.50      | ~ r2_hidden(X0,X2) ),
% 7.41/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_442,plain,
% 7.41/1.50      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 7.41/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | ~ r2_hidden(X2,X1)
% 7.41/1.50      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 7.41/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_426,c_3]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1164,plain,
% 7.41/1.50      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 7.41/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.41/1.50      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1244,plain,
% 7.41/1.50      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 7.41/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.41/1.50      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1164,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_9,plain,
% 7.41/1.50      ( ~ r2_orders_2(X0,X1,X1)
% 7.41/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.50      | ~ l1_orders_2(X0) ),
% 7.41/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_646,plain,
% 7.41/1.50      ( ~ r2_orders_2(X0,X1,X1)
% 7.41/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.41/1.50      | sK3 != X0 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_647,plain,
% 7.41/1.50      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_646]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1155,plain,
% 7.41/1.50      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 7.41/1.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1185,plain,
% 7.41/1.50      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 7.41/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1155,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1835,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 7.41/1.50      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 7.41/1.50      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1244,c_1185]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_19,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 7.41/1.50      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ v5_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_474,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 7.41/1.50      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | sK3 != X1 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_475,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 7.41/1.50      | v2_struct_0(sK3)
% 7.41/1.50      | ~ v3_orders_2(sK3)
% 7.41/1.50      | ~ v4_orders_2(sK3)
% 7.41/1.50      | ~ l1_orders_2(sK3) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_474]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_479,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 7.41/1.50      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_475,c_25,c_24,c_23,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1162,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.41/1.50      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 7.41/1.50      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1219,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 7.41/1.50      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1162,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3482,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 7.41/1.50      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_1835,c_1219]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_8184,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_8178,c_3482]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_8193,plain,
% 7.41/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_8184,c_1366]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3500,plain,
% 7.41/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.41/1.50      inference(instantiation,[status(thm)],[c_874]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_12,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ v5_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_564,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.41/1.50      | v2_struct_0(X1)
% 7.41/1.50      | ~ v3_orders_2(X1)
% 7.41/1.50      | ~ v4_orders_2(X1)
% 7.41/1.50      | ~ l1_orders_2(X1)
% 7.41/1.50      | sK3 != X1 ),
% 7.41/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_565,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | v2_struct_0(sK3)
% 7.41/1.50      | ~ v3_orders_2(sK3)
% 7.41/1.50      | ~ v4_orders_2(sK3)
% 7.41/1.50      | ~ l1_orders_2(sK3) ),
% 7.41/1.50      inference(unflattening,[status(thm)],[c_564]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_569,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.41/1.50      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.41/1.50      inference(global_propositional_subsumption,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_565,c_25,c_24,c_23,c_21]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1158,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.41/1.50      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1195,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.41/1.50      inference(light_normalisation,[status(thm)],[c_1158,c_635]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1,plain,
% 7.41/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.41/1.50      | ~ r2_hidden(X2,X0)
% 7.41/1.50      | r2_hidden(X2,X1) ),
% 7.41/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1169,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.41/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.41/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1820,plain,
% 7.41/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
% 7.41/1.50      | r2_hidden(X1,k2_struct_0(sK3)) = iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1195,c_1169]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3323,plain,
% 7.41/1.50      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 7.41/1.50      | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1178,c_1820]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_3351,plain,
% 7.41/1.50      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 7.41/1.50      inference(superposition,[status(thm)],[c_1166,c_3323]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(c_1344,plain,
% 7.41/1.50      ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 7.41/1.50      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 7.41/1.50      inference(predicate_to_equality,[status(thm)],[c_1343]) ).
% 7.41/1.50  
% 7.41/1.50  cnf(contradiction,plain,
% 7.41/1.50      ( $false ),
% 7.41/1.50      inference(minisat,
% 7.41/1.50                [status(thm)],
% 7.41/1.50                [c_17918,c_8193,c_3500,c_3351,c_1344,c_1178,c_20]) ).
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.41/1.50  
% 7.41/1.50  ------                               Statistics
% 7.41/1.50  
% 7.41/1.50  ------ General
% 7.41/1.50  
% 7.41/1.50  abstr_ref_over_cycles:                  0
% 7.41/1.50  abstr_ref_under_cycles:                 0
% 7.41/1.50  gc_basic_clause_elim:                   0
% 7.41/1.50  forced_gc_time:                         0
% 7.41/1.50  parsing_time:                           0.012
% 7.41/1.50  unif_index_cands_time:                  0.
% 7.41/1.50  unif_index_add_time:                    0.
% 7.41/1.50  orderings_time:                         0.
% 7.41/1.50  out_proof_time:                         0.01
% 7.41/1.50  total_time:                             0.658
% 7.41/1.50  num_of_symbols:                         52
% 7.41/1.50  num_of_terms:                           18428
% 7.41/1.50  
% 7.41/1.50  ------ Preprocessing
% 7.41/1.50  
% 7.41/1.50  num_of_splits:                          0
% 7.41/1.50  num_of_split_atoms:                     0
% 7.41/1.50  num_of_reused_defs:                     0
% 7.41/1.50  num_eq_ax_congr_red:                    28
% 7.41/1.50  num_of_sem_filtered_clauses:            1
% 7.41/1.50  num_of_subtypes:                        0
% 7.41/1.50  monotx_restored_types:                  0
% 7.41/1.50  sat_num_of_epr_types:                   0
% 7.41/1.50  sat_num_of_non_cyclic_types:            0
% 7.41/1.50  sat_guarded_non_collapsed_types:        0
% 7.41/1.50  num_pure_diseq_elim:                    0
% 7.41/1.50  simp_replaced_by:                       0
% 7.41/1.50  res_preprocessed:                       102
% 7.41/1.50  prep_upred:                             0
% 7.41/1.50  prep_unflattend:                        27
% 7.41/1.50  smt_new_axioms:                         0
% 7.41/1.50  pred_elim_cands:                        3
% 7.41/1.50  pred_elim:                              8
% 7.41/1.50  pred_elim_cl:                           9
% 7.41/1.50  pred_elim_cycles:                       11
% 7.41/1.50  merged_defs:                            0
% 7.41/1.50  merged_defs_ncl:                        0
% 7.41/1.50  bin_hyper_res:                          0
% 7.41/1.50  prep_cycles:                            4
% 7.41/1.50  pred_elim_time:                         0.02
% 7.41/1.50  splitting_time:                         0.
% 7.41/1.50  sem_filter_time:                        0.
% 7.41/1.50  monotx_time:                            0.001
% 7.41/1.50  subtype_inf_time:                       0.
% 7.41/1.50  
% 7.41/1.50  ------ Problem properties
% 7.41/1.50  
% 7.41/1.50  clauses:                                17
% 7.41/1.50  conjectures:                            1
% 7.41/1.50  epr:                                    1
% 7.41/1.50  horn:                                   14
% 7.41/1.50  ground:                                 3
% 7.41/1.50  unary:                                  5
% 7.41/1.50  binary:                                 4
% 7.41/1.50  lits:                                   41
% 7.41/1.50  lits_eq:                                5
% 7.41/1.50  fd_pure:                                0
% 7.41/1.50  fd_pseudo:                              0
% 7.41/1.50  fd_cond:                                1
% 7.41/1.50  fd_pseudo_cond:                         0
% 7.41/1.50  ac_symbols:                             0
% 7.41/1.50  
% 7.41/1.50  ------ Propositional Solver
% 7.41/1.50  
% 7.41/1.50  prop_solver_calls:                      30
% 7.41/1.50  prop_fast_solver_calls:                 1165
% 7.41/1.50  smt_solver_calls:                       0
% 7.41/1.50  smt_fast_solver_calls:                  0
% 7.41/1.50  prop_num_of_clauses:                    7332
% 7.41/1.50  prop_preprocess_simplified:             16126
% 7.41/1.50  prop_fo_subsumed:                       40
% 7.41/1.50  prop_solver_time:                       0.
% 7.41/1.50  smt_solver_time:                        0.
% 7.41/1.50  smt_fast_solver_time:                   0.
% 7.41/1.50  prop_fast_solver_time:                  0.
% 7.41/1.50  prop_unsat_core_time:                   0.
% 7.41/1.50  
% 7.41/1.50  ------ QBF
% 7.41/1.50  
% 7.41/1.50  qbf_q_res:                              0
% 7.41/1.50  qbf_num_tautologies:                    0
% 7.41/1.50  qbf_prep_cycles:                        0
% 7.41/1.50  
% 7.41/1.50  ------ BMC1
% 7.41/1.50  
% 7.41/1.50  bmc1_current_bound:                     -1
% 7.41/1.50  bmc1_last_solved_bound:                 -1
% 7.41/1.50  bmc1_unsat_core_size:                   -1
% 7.41/1.50  bmc1_unsat_core_parents_size:           -1
% 7.41/1.50  bmc1_merge_next_fun:                    0
% 7.41/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.41/1.50  
% 7.41/1.50  ------ Instantiation
% 7.41/1.50  
% 7.41/1.50  inst_num_of_clauses:                    2291
% 7.41/1.50  inst_num_in_passive:                    1364
% 7.41/1.50  inst_num_in_active:                     742
% 7.41/1.50  inst_num_in_unprocessed:                184
% 7.41/1.50  inst_num_of_loops:                      893
% 7.41/1.50  inst_num_of_learning_restarts:          0
% 7.41/1.50  inst_num_moves_active_passive:          147
% 7.41/1.50  inst_lit_activity:                      0
% 7.41/1.50  inst_lit_activity_moves:                1
% 7.41/1.50  inst_num_tautologies:                   0
% 7.41/1.50  inst_num_prop_implied:                  0
% 7.41/1.50  inst_num_existing_simplified:           0
% 7.41/1.50  inst_num_eq_res_simplified:             0
% 7.41/1.50  inst_num_child_elim:                    0
% 7.41/1.50  inst_num_of_dismatching_blockings:      864
% 7.41/1.50  inst_num_of_non_proper_insts:           2214
% 7.41/1.50  inst_num_of_duplicates:                 0
% 7.41/1.50  inst_inst_num_from_inst_to_res:         0
% 7.41/1.50  inst_dismatching_checking_time:         0.
% 7.41/1.50  
% 7.41/1.50  ------ Resolution
% 7.41/1.50  
% 7.41/1.50  res_num_of_clauses:                     0
% 7.41/1.50  res_num_in_passive:                     0
% 7.41/1.50  res_num_in_active:                      0
% 7.41/1.50  res_num_of_loops:                       106
% 7.41/1.50  res_forward_subset_subsumed:            134
% 7.41/1.50  res_backward_subset_subsumed:           0
% 7.41/1.50  res_forward_subsumed:                   0
% 7.41/1.50  res_backward_subsumed:                  0
% 7.41/1.50  res_forward_subsumption_resolution:     5
% 7.41/1.50  res_backward_subsumption_resolution:    0
% 7.41/1.50  res_clause_to_clause_subsumption:       1274
% 7.41/1.50  res_orphan_elimination:                 0
% 7.41/1.50  res_tautology_del:                      160
% 7.41/1.50  res_num_eq_res_simplified:              0
% 7.41/1.50  res_num_sel_changes:                    0
% 7.41/1.50  res_moves_from_active_to_pass:          0
% 7.41/1.50  
% 7.41/1.50  ------ Superposition
% 7.41/1.50  
% 7.41/1.50  sup_time_total:                         0.
% 7.41/1.50  sup_time_generating:                    0.
% 7.41/1.50  sup_time_sim_full:                      0.
% 7.41/1.50  sup_time_sim_immed:                     0.
% 7.41/1.50  
% 7.41/1.50  sup_num_of_clauses:                     402
% 7.41/1.50  sup_num_in_active:                      177
% 7.41/1.50  sup_num_in_passive:                     225
% 7.41/1.50  sup_num_of_loops:                       178
% 7.41/1.50  sup_fw_superposition:                   242
% 7.41/1.50  sup_bw_superposition:                   175
% 7.41/1.50  sup_immediate_simplified:               143
% 7.41/1.50  sup_given_eliminated:                   0
% 7.41/1.50  comparisons_done:                       0
% 7.41/1.50  comparisons_avoided:                    60
% 7.41/1.50  
% 7.41/1.50  ------ Simplifications
% 7.41/1.50  
% 7.41/1.50  
% 7.41/1.50  sim_fw_subset_subsumed:                 4
% 7.41/1.50  sim_bw_subset_subsumed:                 3
% 7.41/1.50  sim_fw_subsumed:                        4
% 7.41/1.50  sim_bw_subsumed:                        0
% 7.41/1.50  sim_fw_subsumption_res:                 3
% 7.41/1.50  sim_bw_subsumption_res:                 0
% 7.41/1.50  sim_tautology_del:                      4
% 7.41/1.50  sim_eq_tautology_del:                   1
% 7.41/1.50  sim_eq_res_simp:                        0
% 7.41/1.50  sim_fw_demodulated:                     6
% 7.41/1.50  sim_bw_demodulated:                     0
% 7.41/1.50  sim_light_normalised:                   149
% 7.41/1.50  sim_joinable_taut:                      0
% 7.41/1.50  sim_joinable_simp:                      0
% 7.41/1.50  sim_ac_normalised:                      0
% 7.41/1.50  sim_smt_subsumption:                    0
% 7.41/1.50  
%------------------------------------------------------------------------------
