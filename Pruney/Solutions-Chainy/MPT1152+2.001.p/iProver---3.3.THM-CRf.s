%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:10 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  194 (1066 expanded)
%              Number of clauses        :  112 ( 320 expanded)
%              Number of leaves         :   22 ( 223 expanded)
%              Depth                    :   20
%              Number of atoms          :  744 (4691 expanded)
%              Number of equality atoms :  206 ( 999 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f43])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4))
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f52])).

fof(f86,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1355,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_352,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_696,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_29])).

cnf(c_697,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_1345,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_363,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_21,c_14])).

cnf(c_691,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_29])).

cnf(c_692,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_1375,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1345,c_692])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_33,c_32,c_31,c_29])).

cnf(c_1347,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1430,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1347,c_692])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1357,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4381,plain,
    ( m1_subset_1(X0,k2_struct_0(sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1357])).

cnf(c_4824,plain,
    ( m1_subset_1(X0,k2_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_4381])).

cnf(c_4853,plain,
    ( k2_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0
    | m1_subset_1(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_4824])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_972,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1599,plain,
    ( k2_orders_2(sK4,k2_struct_0(sK4)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1600,plain,
    ( k2_orders_2(sK4,k2_struct_0(sK4)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_8936,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_28,c_106,c_107,c_1600])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8942,plain,
    ( r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8936,c_1359])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | sK3(X1,sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
    | sK3(X1,sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_33,c_32,c_31,c_29])).

cnf(c_1350,plain,
    ( sK3(X0,sK4,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1447,plain,
    ( sK3(X0,sK4,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1350,c_692])).

cnf(c_1677,plain,
    ( sK3(sK1(a_2_1_orders_2(sK4,X0)),sK4,X0) = sK1(a_2_1_orders_2(sK4,X0))
    | a_2_1_orders_2(sK4,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1447])).

cnf(c_2196,plain,
    ( sK3(sK1(a_2_1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(a_2_1_orders_2(sK4,k2_struct_0(sK4)))
    | a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1375,c_1677])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_33,c_32,c_31,c_29])).

cnf(c_1346,plain,
    ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1407,plain,
    ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1346,c_692])).

cnf(c_1613,plain,
    ( a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k2_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1375,c_1407])).

cnf(c_2206,plain,
    ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4)))
    | a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2196,c_1613])).

cnf(c_2207,plain,
    ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4)))
    | k2_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2206,c_1613])).

cnf(c_7573,plain,
    ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_28,c_106,c_107,c_1600])).

cnf(c_25,plain,
    ( r2_orders_2(X0,sK3(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_478,plain,
    ( r2_orders_2(X0,sK3(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_479,plain,
    ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_33,c_32,c_31,c_29])).

cnf(c_499,plain,
    ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_11])).

cnf(c_1353,plain,
    ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1479,plain,
    ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1353,c_692])).

cnf(c_17,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_703,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_704,plain,
    ( ~ r2_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_1344,plain,
    ( r2_orders_2(sK4,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1402,plain,
    ( r2_orders_2(sK4,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1344,c_692])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top
    | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1402])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_33,c_32,c_31,c_29])).

cnf(c_1351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1454,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1351,c_692])).

cnf(c_2954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top
    | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_1454])).

cnf(c_7579,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),a_2_1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_2954])).

cnf(c_7588,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7579,c_1613])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4660,plain,
    ( ~ r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4))
    | ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4666,plain,
    ( r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4660])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2740,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(u1_struct_0(sK4),X2)
    | X2 != X1
    | u1_struct_0(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_2742,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1364,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1362,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2349,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1362])).

cnf(c_2484,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_2349])).

cnf(c_2496,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2484])).

cnf(c_2125,plain,
    ( r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4))
    | k1_xboole_0 = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2126,plain,
    ( k1_xboole_0 = k2_struct_0(sK4)
    | r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_1707,plain,
    ( X0 != X1
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2015,plain,
    ( X0 != k2_struct_0(sK4)
    | u1_struct_0(sK4) = X0
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_2016,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | u1_struct_0(sK4) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1662,plain,
    ( ~ m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1900,plain,
    ( ~ m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1682,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1687,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_xboole_0)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_1590,plain,
    ( r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
    | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1591,plain,
    ( k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4))
    | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1590])).

cnf(c_1560,plain,
    ( m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8942,c_7588,c_4666,c_2742,c_2496,c_2126,c_2016,c_1900,c_1687,c_1591,c_1590,c_1560,c_1375,c_697,c_692,c_107,c_106,c_101,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:51:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.22/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.98  
% 3.22/0.98  ------  iProver source info
% 3.22/0.98  
% 3.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.98  git: non_committed_changes: false
% 3.22/0.98  git: last_make_outside_of_git: false
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.99  --trig_cnt_out                          false
% 3.22/0.99  --trig_cnt_out_tolerance                1.
% 3.22/0.99  --trig_cnt_out_sk_spl                   false
% 3.22/0.99  --abstr_cl_out                          false
% 3.22/0.99  
% 3.22/0.99  ------ Global Options
% 3.22/0.99  
% 3.22/0.99  --schedule                              default
% 3.22/0.99  --add_important_lit                     false
% 3.22/0.99  --prop_solver_per_cl                    1000
% 3.22/0.99  --min_unsat_core                        false
% 3.22/0.99  --soft_assumptions                      false
% 3.22/0.99  --soft_lemma_size                       3
% 3.22/0.99  --prop_impl_unit_size                   0
% 3.22/0.99  --prop_impl_unit                        []
% 3.22/0.99  --share_sel_clauses                     true
% 3.22/0.99  --reset_solvers                         false
% 3.22/0.99  --bc_imp_inh                            [conj_cone]
% 3.22/0.99  --conj_cone_tolerance                   3.
% 3.22/0.99  --extra_neg_conj                        none
% 3.22/0.99  --large_theory_mode                     true
% 3.22/0.99  --prolific_symb_bound                   200
% 3.22/0.99  --lt_threshold                          2000
% 3.22/0.99  --clause_weak_htbl                      true
% 3.22/0.99  --gc_record_bc_elim                     false
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing Options
% 3.22/0.99  
% 3.22/0.99  --preprocessing_flag                    true
% 3.22/0.99  --time_out_prep_mult                    0.1
% 3.22/0.99  --splitting_mode                        input
% 3.22/0.99  --splitting_grd                         true
% 3.22/0.99  --splitting_cvd                         false
% 3.22/0.99  --splitting_cvd_svl                     false
% 3.22/0.99  --splitting_nvd                         32
% 3.22/0.99  --sub_typing                            true
% 3.22/0.99  --prep_gs_sim                           true
% 3.22/0.99  --prep_unflatten                        true
% 3.22/0.99  --prep_res_sim                          true
% 3.22/0.99  --prep_upred                            true
% 3.22/0.99  --prep_sem_filter                       exhaustive
% 3.22/0.99  --prep_sem_filter_out                   false
% 3.22/0.99  --pred_elim                             true
% 3.22/0.99  --res_sim_input                         true
% 3.22/0.99  --eq_ax_congr_red                       true
% 3.22/0.99  --pure_diseq_elim                       true
% 3.22/0.99  --brand_transform                       false
% 3.22/0.99  --non_eq_to_eq                          false
% 3.22/0.99  --prep_def_merge                        true
% 3.22/0.99  --prep_def_merge_prop_impl              false
% 3.22/0.99  --prep_def_merge_mbd                    true
% 3.22/0.99  --prep_def_merge_tr_red                 false
% 3.22/0.99  --prep_def_merge_tr_cl                  false
% 3.22/0.99  --smt_preprocessing                     true
% 3.22/0.99  --smt_ac_axioms                         fast
% 3.22/0.99  --preprocessed_out                      false
% 3.22/0.99  --preprocessed_stats                    false
% 3.22/0.99  
% 3.22/0.99  ------ Abstraction refinement Options
% 3.22/0.99  
% 3.22/0.99  --abstr_ref                             []
% 3.22/0.99  --abstr_ref_prep                        false
% 3.22/0.99  --abstr_ref_until_sat                   false
% 3.22/0.99  --abstr_ref_sig_restrict                funpre
% 3.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.99  --abstr_ref_under                       []
% 3.22/0.99  
% 3.22/0.99  ------ SAT Options
% 3.22/0.99  
% 3.22/0.99  --sat_mode                              false
% 3.22/0.99  --sat_fm_restart_options                ""
% 3.22/0.99  --sat_gr_def                            false
% 3.22/0.99  --sat_epr_types                         true
% 3.22/0.99  --sat_non_cyclic_types                  false
% 3.22/0.99  --sat_finite_models                     false
% 3.22/0.99  --sat_fm_lemmas                         false
% 3.22/0.99  --sat_fm_prep                           false
% 3.22/0.99  --sat_fm_uc_incr                        true
% 3.22/0.99  --sat_out_model                         small
% 3.22/0.99  --sat_out_clauses                       false
% 3.22/0.99  
% 3.22/0.99  ------ QBF Options
% 3.22/0.99  
% 3.22/0.99  --qbf_mode                              false
% 3.22/0.99  --qbf_elim_univ                         false
% 3.22/0.99  --qbf_dom_inst                          none
% 3.22/0.99  --qbf_dom_pre_inst                      false
% 3.22/0.99  --qbf_sk_in                             false
% 3.22/0.99  --qbf_pred_elim                         true
% 3.22/0.99  --qbf_split                             512
% 3.22/0.99  
% 3.22/0.99  ------ BMC1 Options
% 3.22/0.99  
% 3.22/0.99  --bmc1_incremental                      false
% 3.22/0.99  --bmc1_axioms                           reachable_all
% 3.22/0.99  --bmc1_min_bound                        0
% 3.22/0.99  --bmc1_max_bound                        -1
% 3.22/0.99  --bmc1_max_bound_default                -1
% 3.22/0.99  --bmc1_symbol_reachability              true
% 3.22/0.99  --bmc1_property_lemmas                  false
% 3.22/0.99  --bmc1_k_induction                      false
% 3.22/0.99  --bmc1_non_equiv_states                 false
% 3.22/0.99  --bmc1_deadlock                         false
% 3.22/0.99  --bmc1_ucm                              false
% 3.22/0.99  --bmc1_add_unsat_core                   none
% 3.22/0.99  --bmc1_unsat_core_children              false
% 3.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.99  --bmc1_out_stat                         full
% 3.22/0.99  --bmc1_ground_init                      false
% 3.22/0.99  --bmc1_pre_inst_next_state              false
% 3.22/0.99  --bmc1_pre_inst_state                   false
% 3.22/0.99  --bmc1_pre_inst_reach_state             false
% 3.22/0.99  --bmc1_out_unsat_core                   false
% 3.22/0.99  --bmc1_aig_witness_out                  false
% 3.22/0.99  --bmc1_verbose                          false
% 3.22/0.99  --bmc1_dump_clauses_tptp                false
% 3.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.99  --bmc1_dump_file                        -
% 3.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.99  --bmc1_ucm_extend_mode                  1
% 3.22/0.99  --bmc1_ucm_init_mode                    2
% 3.22/0.99  --bmc1_ucm_cone_mode                    none
% 3.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.99  --bmc1_ucm_relax_model                  4
% 3.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.99  --bmc1_ucm_layered_model                none
% 3.22/0.99  --bmc1_ucm_max_lemma_size               10
% 3.22/0.99  
% 3.22/0.99  ------ AIG Options
% 3.22/0.99  
% 3.22/0.99  --aig_mode                              false
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation Options
% 3.22/0.99  
% 3.22/0.99  --instantiation_flag                    true
% 3.22/0.99  --inst_sos_flag                         false
% 3.22/0.99  --inst_sos_phase                        true
% 3.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel_side                     num_symb
% 3.22/0.99  --inst_solver_per_active                1400
% 3.22/0.99  --inst_solver_calls_frac                1.
% 3.22/0.99  --inst_passive_queue_type               priority_queues
% 3.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.99  --inst_passive_queues_freq              [25;2]
% 3.22/0.99  --inst_dismatching                      true
% 3.22/0.99  --inst_eager_unprocessed_to_passive     true
% 3.22/0.99  --inst_prop_sim_given                   true
% 3.22/0.99  --inst_prop_sim_new                     false
% 3.22/0.99  --inst_subs_new                         false
% 3.22/0.99  --inst_eq_res_simp                      false
% 3.22/0.99  --inst_subs_given                       false
% 3.22/0.99  --inst_orphan_elimination               true
% 3.22/0.99  --inst_learning_loop_flag               true
% 3.22/0.99  --inst_learning_start                   3000
% 3.22/0.99  --inst_learning_factor                  2
% 3.22/0.99  --inst_start_prop_sim_after_learn       3
% 3.22/0.99  --inst_sel_renew                        solver
% 3.22/0.99  --inst_lit_activity_flag                true
% 3.22/0.99  --inst_restr_to_given                   false
% 3.22/0.99  --inst_activity_threshold               500
% 3.22/0.99  --inst_out_proof                        true
% 3.22/0.99  
% 3.22/0.99  ------ Resolution Options
% 3.22/0.99  
% 3.22/0.99  --resolution_flag                       true
% 3.22/0.99  --res_lit_sel                           adaptive
% 3.22/0.99  --res_lit_sel_side                      none
% 3.22/0.99  --res_ordering                          kbo
% 3.22/0.99  --res_to_prop_solver                    active
% 3.22/0.99  --res_prop_simpl_new                    false
% 3.22/0.99  --res_prop_simpl_given                  true
% 3.22/0.99  --res_passive_queue_type                priority_queues
% 3.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.99  --res_passive_queues_freq               [15;5]
% 3.22/0.99  --res_forward_subs                      full
% 3.22/0.99  --res_backward_subs                     full
% 3.22/0.99  --res_forward_subs_resolution           true
% 3.22/0.99  --res_backward_subs_resolution          true
% 3.22/0.99  --res_orphan_elimination                true
% 3.22/0.99  --res_time_limit                        2.
% 3.22/0.99  --res_out_proof                         true
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Options
% 3.22/0.99  
% 3.22/0.99  --superposition_flag                    true
% 3.22/0.99  --sup_passive_queue_type                priority_queues
% 3.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.99  --demod_completeness_check              fast
% 3.22/0.99  --demod_use_ground                      true
% 3.22/0.99  --sup_to_prop_solver                    passive
% 3.22/0.99  --sup_prop_simpl_new                    true
% 3.22/0.99  --sup_prop_simpl_given                  true
% 3.22/0.99  --sup_fun_splitting                     false
% 3.22/0.99  --sup_smt_interval                      50000
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Simplification Setup
% 3.22/0.99  
% 3.22/0.99  --sup_indices_passive                   []
% 3.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_full_bw                           [BwDemod]
% 3.22/0.99  --sup_immed_triv                        [TrivRules]
% 3.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_immed_bw_main                     []
% 3.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  
% 3.22/0.99  ------ Combination Options
% 3.22/0.99  
% 3.22/0.99  --comb_res_mult                         3
% 3.22/0.99  --comb_sup_mult                         2
% 3.22/0.99  --comb_inst_mult                        10
% 3.22/0.99  
% 3.22/0.99  ------ Debug Options
% 3.22/0.99  
% 3.22/0.99  --dbg_backtrace                         false
% 3.22/0.99  --dbg_dump_prop_clauses                 false
% 3.22/0.99  --dbg_dump_prop_clauses_file            -
% 3.22/0.99  --dbg_out_stat                          false
% 3.22/0.99  ------ Parsing...
% 3.22/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.99  ------ Proving...
% 3.22/0.99  ------ Problem Properties 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  clauses                                 26
% 3.22/0.99  conjectures                             1
% 3.22/0.99  EPR                                     5
% 3.22/0.99  Horn                                    20
% 3.22/0.99  unary                                   7
% 3.22/0.99  binary                                  7
% 3.22/0.99  lits                                    61
% 3.22/0.99  lits eq                                 10
% 3.22/0.99  fd_pure                                 0
% 3.22/0.99  fd_pseudo                               0
% 3.22/0.99  fd_cond                                 2
% 3.22/0.99  fd_pseudo_cond                          0
% 3.22/0.99  AC symbols                              0
% 3.22/0.99  
% 3.22/0.99  ------ Schedule dynamic 5 is on 
% 3.22/0.99  
% 3.22/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  Current options:
% 3.22/0.99  ------ 
% 3.22/0.99  
% 3.22/0.99  ------ Input Options
% 3.22/0.99  
% 3.22/0.99  --out_options                           all
% 3.22/0.99  --tptp_safe_out                         true
% 3.22/0.99  --problem_path                          ""
% 3.22/0.99  --include_path                          ""
% 3.22/0.99  --clausifier                            res/vclausify_rel
% 3.22/0.99  --clausifier_options                    --mode clausify
% 3.22/0.99  --stdin                                 false
% 3.22/0.99  --stats_out                             all
% 3.22/0.99  
% 3.22/0.99  ------ General Options
% 3.22/0.99  
% 3.22/0.99  --fof                                   false
% 3.22/0.99  --time_out_real                         305.
% 3.22/0.99  --time_out_virtual                      -1.
% 3.22/0.99  --symbol_type_check                     false
% 3.22/0.99  --clausify_out                          false
% 3.22/0.99  --sig_cnt_out                           false
% 3.22/0.99  --trig_cnt_out                          false
% 3.22/0.99  --trig_cnt_out_tolerance                1.
% 3.22/0.99  --trig_cnt_out_sk_spl                   false
% 3.22/0.99  --abstr_cl_out                          false
% 3.22/0.99  
% 3.22/0.99  ------ Global Options
% 3.22/0.99  
% 3.22/0.99  --schedule                              default
% 3.22/0.99  --add_important_lit                     false
% 3.22/0.99  --prop_solver_per_cl                    1000
% 3.22/0.99  --min_unsat_core                        false
% 3.22/0.99  --soft_assumptions                      false
% 3.22/0.99  --soft_lemma_size                       3
% 3.22/0.99  --prop_impl_unit_size                   0
% 3.22/0.99  --prop_impl_unit                        []
% 3.22/0.99  --share_sel_clauses                     true
% 3.22/0.99  --reset_solvers                         false
% 3.22/0.99  --bc_imp_inh                            [conj_cone]
% 3.22/0.99  --conj_cone_tolerance                   3.
% 3.22/0.99  --extra_neg_conj                        none
% 3.22/0.99  --large_theory_mode                     true
% 3.22/0.99  --prolific_symb_bound                   200
% 3.22/0.99  --lt_threshold                          2000
% 3.22/0.99  --clause_weak_htbl                      true
% 3.22/0.99  --gc_record_bc_elim                     false
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing Options
% 3.22/0.99  
% 3.22/0.99  --preprocessing_flag                    true
% 3.22/0.99  --time_out_prep_mult                    0.1
% 3.22/0.99  --splitting_mode                        input
% 3.22/0.99  --splitting_grd                         true
% 3.22/0.99  --splitting_cvd                         false
% 3.22/0.99  --splitting_cvd_svl                     false
% 3.22/0.99  --splitting_nvd                         32
% 3.22/0.99  --sub_typing                            true
% 3.22/0.99  --prep_gs_sim                           true
% 3.22/0.99  --prep_unflatten                        true
% 3.22/0.99  --prep_res_sim                          true
% 3.22/0.99  --prep_upred                            true
% 3.22/0.99  --prep_sem_filter                       exhaustive
% 3.22/0.99  --prep_sem_filter_out                   false
% 3.22/0.99  --pred_elim                             true
% 3.22/0.99  --res_sim_input                         true
% 3.22/0.99  --eq_ax_congr_red                       true
% 3.22/0.99  --pure_diseq_elim                       true
% 3.22/0.99  --brand_transform                       false
% 3.22/0.99  --non_eq_to_eq                          false
% 3.22/0.99  --prep_def_merge                        true
% 3.22/0.99  --prep_def_merge_prop_impl              false
% 3.22/0.99  --prep_def_merge_mbd                    true
% 3.22/0.99  --prep_def_merge_tr_red                 false
% 3.22/0.99  --prep_def_merge_tr_cl                  false
% 3.22/0.99  --smt_preprocessing                     true
% 3.22/0.99  --smt_ac_axioms                         fast
% 3.22/0.99  --preprocessed_out                      false
% 3.22/0.99  --preprocessed_stats                    false
% 3.22/0.99  
% 3.22/0.99  ------ Abstraction refinement Options
% 3.22/0.99  
% 3.22/0.99  --abstr_ref                             []
% 3.22/0.99  --abstr_ref_prep                        false
% 3.22/0.99  --abstr_ref_until_sat                   false
% 3.22/0.99  --abstr_ref_sig_restrict                funpre
% 3.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.99  --abstr_ref_under                       []
% 3.22/0.99  
% 3.22/0.99  ------ SAT Options
% 3.22/0.99  
% 3.22/0.99  --sat_mode                              false
% 3.22/0.99  --sat_fm_restart_options                ""
% 3.22/0.99  --sat_gr_def                            false
% 3.22/0.99  --sat_epr_types                         true
% 3.22/0.99  --sat_non_cyclic_types                  false
% 3.22/0.99  --sat_finite_models                     false
% 3.22/0.99  --sat_fm_lemmas                         false
% 3.22/0.99  --sat_fm_prep                           false
% 3.22/0.99  --sat_fm_uc_incr                        true
% 3.22/0.99  --sat_out_model                         small
% 3.22/0.99  --sat_out_clauses                       false
% 3.22/0.99  
% 3.22/0.99  ------ QBF Options
% 3.22/0.99  
% 3.22/0.99  --qbf_mode                              false
% 3.22/0.99  --qbf_elim_univ                         false
% 3.22/0.99  --qbf_dom_inst                          none
% 3.22/0.99  --qbf_dom_pre_inst                      false
% 3.22/0.99  --qbf_sk_in                             false
% 3.22/0.99  --qbf_pred_elim                         true
% 3.22/0.99  --qbf_split                             512
% 3.22/0.99  
% 3.22/0.99  ------ BMC1 Options
% 3.22/0.99  
% 3.22/0.99  --bmc1_incremental                      false
% 3.22/0.99  --bmc1_axioms                           reachable_all
% 3.22/0.99  --bmc1_min_bound                        0
% 3.22/0.99  --bmc1_max_bound                        -1
% 3.22/0.99  --bmc1_max_bound_default                -1
% 3.22/0.99  --bmc1_symbol_reachability              true
% 3.22/0.99  --bmc1_property_lemmas                  false
% 3.22/0.99  --bmc1_k_induction                      false
% 3.22/0.99  --bmc1_non_equiv_states                 false
% 3.22/0.99  --bmc1_deadlock                         false
% 3.22/0.99  --bmc1_ucm                              false
% 3.22/0.99  --bmc1_add_unsat_core                   none
% 3.22/0.99  --bmc1_unsat_core_children              false
% 3.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.99  --bmc1_out_stat                         full
% 3.22/0.99  --bmc1_ground_init                      false
% 3.22/0.99  --bmc1_pre_inst_next_state              false
% 3.22/0.99  --bmc1_pre_inst_state                   false
% 3.22/0.99  --bmc1_pre_inst_reach_state             false
% 3.22/0.99  --bmc1_out_unsat_core                   false
% 3.22/0.99  --bmc1_aig_witness_out                  false
% 3.22/0.99  --bmc1_verbose                          false
% 3.22/0.99  --bmc1_dump_clauses_tptp                false
% 3.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.99  --bmc1_dump_file                        -
% 3.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.99  --bmc1_ucm_extend_mode                  1
% 3.22/0.99  --bmc1_ucm_init_mode                    2
% 3.22/0.99  --bmc1_ucm_cone_mode                    none
% 3.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.99  --bmc1_ucm_relax_model                  4
% 3.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.99  --bmc1_ucm_layered_model                none
% 3.22/0.99  --bmc1_ucm_max_lemma_size               10
% 3.22/0.99  
% 3.22/0.99  ------ AIG Options
% 3.22/0.99  
% 3.22/0.99  --aig_mode                              false
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation Options
% 3.22/0.99  
% 3.22/0.99  --instantiation_flag                    true
% 3.22/0.99  --inst_sos_flag                         false
% 3.22/0.99  --inst_sos_phase                        true
% 3.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel_side                     none
% 3.22/0.99  --inst_solver_per_active                1400
% 3.22/0.99  --inst_solver_calls_frac                1.
% 3.22/0.99  --inst_passive_queue_type               priority_queues
% 3.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.99  --inst_passive_queues_freq              [25;2]
% 3.22/0.99  --inst_dismatching                      true
% 3.22/0.99  --inst_eager_unprocessed_to_passive     true
% 3.22/0.99  --inst_prop_sim_given                   true
% 3.22/0.99  --inst_prop_sim_new                     false
% 3.22/0.99  --inst_subs_new                         false
% 3.22/0.99  --inst_eq_res_simp                      false
% 3.22/0.99  --inst_subs_given                       false
% 3.22/0.99  --inst_orphan_elimination               true
% 3.22/0.99  --inst_learning_loop_flag               true
% 3.22/0.99  --inst_learning_start                   3000
% 3.22/0.99  --inst_learning_factor                  2
% 3.22/0.99  --inst_start_prop_sim_after_learn       3
% 3.22/0.99  --inst_sel_renew                        solver
% 3.22/0.99  --inst_lit_activity_flag                true
% 3.22/0.99  --inst_restr_to_given                   false
% 3.22/0.99  --inst_activity_threshold               500
% 3.22/0.99  --inst_out_proof                        true
% 3.22/0.99  
% 3.22/0.99  ------ Resolution Options
% 3.22/0.99  
% 3.22/0.99  --resolution_flag                       false
% 3.22/0.99  --res_lit_sel                           adaptive
% 3.22/0.99  --res_lit_sel_side                      none
% 3.22/0.99  --res_ordering                          kbo
% 3.22/0.99  --res_to_prop_solver                    active
% 3.22/0.99  --res_prop_simpl_new                    false
% 3.22/0.99  --res_prop_simpl_given                  true
% 3.22/0.99  --res_passive_queue_type                priority_queues
% 3.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.99  --res_passive_queues_freq               [15;5]
% 3.22/0.99  --res_forward_subs                      full
% 3.22/0.99  --res_backward_subs                     full
% 3.22/0.99  --res_forward_subs_resolution           true
% 3.22/0.99  --res_backward_subs_resolution          true
% 3.22/0.99  --res_orphan_elimination                true
% 3.22/0.99  --res_time_limit                        2.
% 3.22/0.99  --res_out_proof                         true
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Options
% 3.22/0.99  
% 3.22/0.99  --superposition_flag                    true
% 3.22/0.99  --sup_passive_queue_type                priority_queues
% 3.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.99  --demod_completeness_check              fast
% 3.22/0.99  --demod_use_ground                      true
% 3.22/0.99  --sup_to_prop_solver                    passive
% 3.22/0.99  --sup_prop_simpl_new                    true
% 3.22/0.99  --sup_prop_simpl_given                  true
% 3.22/0.99  --sup_fun_splitting                     false
% 3.22/0.99  --sup_smt_interval                      50000
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Simplification Setup
% 3.22/0.99  
% 3.22/0.99  --sup_indices_passive                   []
% 3.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_full_bw                           [BwDemod]
% 3.22/0.99  --sup_immed_triv                        [TrivRules]
% 3.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_immed_bw_main                     []
% 3.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  
% 3.22/0.99  ------ Combination Options
% 3.22/0.99  
% 3.22/0.99  --comb_res_mult                         3
% 3.22/0.99  --comb_sup_mult                         2
% 3.22/0.99  --comb_inst_mult                        10
% 3.22/0.99  
% 3.22/0.99  ------ Debug Options
% 3.22/0.99  
% 3.22/0.99  --dbg_backtrace                         false
% 3.22/0.99  --dbg_dump_prop_clauses                 false
% 3.22/0.99  --dbg_dump_prop_clauses_file            -
% 3.22/0.99  --dbg_out_stat                          false
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ Proving...
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS status Theorem for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  fof(f8,axiom,(
% 3.22/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f18,plain,(
% 3.22/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.22/0.99    inference(pure_predicate_removal,[],[f8])).
% 3.22/0.99  
% 3.22/0.99  fof(f23,plain,(
% 3.22/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.22/0.99    inference(ennf_transformation,[],[f18])).
% 3.22/0.99  
% 3.22/0.99  fof(f43,plain,(
% 3.22/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f44,plain,(
% 3.22/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f43])).
% 3.22/0.99  
% 3.22/0.99  fof(f67,plain,(
% 3.22/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f44])).
% 3.22/0.99  
% 3.22/0.99  fof(f14,axiom,(
% 3.22/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f31,plain,(
% 3.22/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f14])).
% 3.22/0.99  
% 3.22/0.99  fof(f75,plain,(
% 3.22/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f31])).
% 3.22/0.99  
% 3.22/0.99  fof(f10,axiom,(
% 3.22/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f25,plain,(
% 3.22/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f10])).
% 3.22/0.99  
% 3.22/0.99  fof(f69,plain,(
% 3.22/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f25])).
% 3.22/0.99  
% 3.22/0.99  fof(f16,conjecture,(
% 3.22/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f17,negated_conjecture,(
% 3.22/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.22/0.99    inference(negated_conjecture,[],[f16])).
% 3.22/0.99  
% 3.22/0.99  fof(f34,plain,(
% 3.22/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f17])).
% 3.22/0.99  
% 3.22/0.99  fof(f35,plain,(
% 3.22/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.22/0.99    inference(flattening,[],[f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f52,plain,(
% 3.22/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f53,plain,(
% 3.22/0.99    k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f52])).
% 3.22/0.99  
% 3.22/0.99  fof(f86,plain,(
% 3.22/0.99    l1_orders_2(sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f9,axiom,(
% 3.22/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f24,plain,(
% 3.22/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f9])).
% 3.22/0.99  
% 3.22/0.99  fof(f68,plain,(
% 3.22/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f24])).
% 3.22/0.99  
% 3.22/0.99  fof(f13,axiom,(
% 3.22/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f29,plain,(
% 3.22/0.99    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f13])).
% 3.22/0.99  
% 3.22/0.99  fof(f30,plain,(
% 3.22/0.99    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.22/0.99    inference(flattening,[],[f29])).
% 3.22/0.99  
% 3.22/0.99  fof(f74,plain,(
% 3.22/0.99    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f30])).
% 3.22/0.99  
% 3.22/0.99  fof(f85,plain,(
% 3.22/0.99    v5_orders_2(sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f82,plain,(
% 3.22/0.99    ~v2_struct_0(sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f83,plain,(
% 3.22/0.99    v3_orders_2(sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f84,plain,(
% 3.22/0.99    v4_orders_2(sK4)),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f6,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f20,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.22/0.99    inference(ennf_transformation,[],[f6])).
% 3.22/0.99  
% 3.22/0.99  fof(f21,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.22/0.99    inference(flattening,[],[f20])).
% 3.22/0.99  
% 3.22/0.99  fof(f65,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f21])).
% 3.22/0.99  
% 3.22/0.99  fof(f87,plain,(
% 3.22/0.99    k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4))),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f2,axiom,(
% 3.22/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f40,plain,(
% 3.22/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.22/0.99    inference(nnf_transformation,[],[f2])).
% 3.22/0.99  
% 3.22/0.99  fof(f41,plain,(
% 3.22/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.22/0.99    inference(flattening,[],[f40])).
% 3.22/0.99  
% 3.22/0.99  fof(f56,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f41])).
% 3.22/0.99  
% 3.22/0.99  fof(f57,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f41])).
% 3.22/0.99  
% 3.22/0.99  fof(f89,plain,(
% 3.22/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.22/0.99    inference(equality_resolution,[],[f57])).
% 3.22/0.99  
% 3.22/0.99  fof(f4,axiom,(
% 3.22/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f19,plain,(
% 3.22/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f4])).
% 3.22/0.99  
% 3.22/0.99  fof(f42,plain,(
% 3.22/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.22/0.99    inference(nnf_transformation,[],[f19])).
% 3.22/0.99  
% 3.22/0.99  fof(f60,plain,(
% 3.22/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f42])).
% 3.22/0.99  
% 3.22/0.99  fof(f15,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f32,plain,(
% 3.22/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.22/0.99    inference(ennf_transformation,[],[f15])).
% 3.22/0.99  
% 3.22/0.99  fof(f33,plain,(
% 3.22/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.22/0.99    inference(flattening,[],[f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f47,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.22/0.99    inference(nnf_transformation,[],[f33])).
% 3.22/0.99  
% 3.22/0.99  fof(f48,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.22/0.99    inference(rectify,[],[f47])).
% 3.22/0.99  
% 3.22/0.99  fof(f50,plain,(
% 3.22/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f49,plain,(
% 3.22/0.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f51,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).
% 3.22/0.99  
% 3.22/0.99  fof(f77,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f51])).
% 3.22/0.99  
% 3.22/0.99  fof(f12,axiom,(
% 3.22/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f27,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f12])).
% 3.22/0.99  
% 3.22/0.99  fof(f28,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.22/0.99    inference(flattening,[],[f27])).
% 3.22/0.99  
% 3.22/0.99  fof(f73,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f28])).
% 3.22/0.99  
% 3.22/0.99  fof(f78,plain,(
% 3.22/0.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f51])).
% 3.22/0.99  
% 3.22/0.99  fof(f11,axiom,(
% 3.22/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f26,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f11])).
% 3.22/0.99  
% 3.22/0.99  fof(f45,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.22/0.99    inference(nnf_transformation,[],[f26])).
% 3.22/0.99  
% 3.22/0.99  fof(f46,plain,(
% 3.22/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.22/0.99    inference(flattening,[],[f45])).
% 3.22/0.99  
% 3.22/0.99  fof(f71,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f46])).
% 3.22/0.99  
% 3.22/0.99  fof(f90,plain,(
% 3.22/0.99    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.22/0.99    inference(equality_resolution,[],[f71])).
% 3.22/0.99  
% 3.22/0.99  fof(f76,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f51])).
% 3.22/0.99  
% 3.22/0.99  fof(f1,axiom,(
% 3.22/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f36,plain,(
% 3.22/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.22/0.99    inference(nnf_transformation,[],[f1])).
% 3.22/0.99  
% 3.22/0.99  fof(f37,plain,(
% 3.22/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.22/0.99    inference(rectify,[],[f36])).
% 3.22/0.99  
% 3.22/0.99  fof(f38,plain,(
% 3.22/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f39,plain,(
% 3.22/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.22/0.99  
% 3.22/0.99  fof(f54,plain,(
% 3.22/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f39])).
% 3.22/0.99  
% 3.22/0.99  fof(f55,plain,(
% 3.22/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f39])).
% 3.22/0.99  
% 3.22/0.99  fof(f58,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.22/0.99    inference(cnf_transformation,[],[f41])).
% 3.22/0.99  
% 3.22/0.99  fof(f88,plain,(
% 3.22/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.22/0.99    inference(equality_resolution,[],[f58])).
% 3.22/0.99  
% 3.22/0.99  fof(f3,axiom,(
% 3.22/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f59,plain,(
% 3.22/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f3])).
% 3.22/0.99  
% 3.22/0.99  fof(f7,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f22,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.22/0.99    inference(ennf_transformation,[],[f7])).
% 3.22/0.99  
% 3.22/0.99  fof(f66,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f22])).
% 3.22/0.99  
% 3.22/0.99  fof(f62,plain,(
% 3.22/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f42])).
% 3.22/0.99  
% 3.22/0.99  fof(f63,plain,(
% 3.22/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f42])).
% 3.22/0.99  
% 3.22/0.99  cnf(c_13,plain,
% 3.22/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1355,plain,
% 3.22/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_21,plain,
% 3.22/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_15,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | ~ l1_struct_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_352,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | ~ l1_orders_2(X0) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_29,negated_conjecture,
% 3.22/0.99      ( l1_orders_2(sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_696,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | sK4 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_352,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_697,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_696]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1345,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_14,plain,
% 3.22/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_363,plain,
% 3.22/0.99      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_21,c_14]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_691,plain,
% 3.22/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_363,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_692,plain,
% 3.22/0.99      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_691]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1375,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1345,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_20,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ v5_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_30,negated_conjecture,
% 3.22/0.99      ( v5_orders_2(sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_621,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_622,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | v2_struct_0(sK4)
% 3.22/0.99      | ~ v3_orders_2(sK4)
% 3.22/0.99      | ~ v4_orders_2(sK4)
% 3.22/0.99      | ~ l1_orders_2(sK4) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_621]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_33,negated_conjecture,
% 3.22/0.99      ( ~ v2_struct_0(sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_32,negated_conjecture,
% 3.22/0.99      ( v3_orders_2(sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_31,negated_conjecture,
% 3.22/0.99      ( v4_orders_2(sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_626,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_622,c_33,c_32,c_31,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1347,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.22/0.99      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1430,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1347,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_11,plain,
% 3.22/0.99      ( m1_subset_1(X0,X1)
% 3.22/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.22/0.99      | ~ r2_hidden(X0,X2) ),
% 3.22/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1357,plain,
% 3.22/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.22/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.22/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4381,plain,
% 3.22/0.99      ( m1_subset_1(X0,k2_struct_0(sK4)) = iProver_top
% 3.22/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X0,k2_orders_2(sK4,X1)) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1430,c_1357]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4824,plain,
% 3.22/0.99      ( m1_subset_1(X0,k2_struct_0(sK4)) = iProver_top
% 3.22/0.99      | r2_hidden(X0,k2_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1375,c_4381]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4853,plain,
% 3.22/0.99      ( k2_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0
% 3.22/0.99      | m1_subset_1(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1355,c_4824]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_28,negated_conjecture,
% 3.22/0.99      ( k1_xboole_0 != k2_orders_2(sK4,k2_struct_0(sK4)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4,plain,
% 3.22/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_106,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_107,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_972,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1599,plain,
% 3.22/0.99      ( k2_orders_2(sK4,k2_struct_0(sK4)) != X0
% 3.22/0.99      | k1_xboole_0 != X0
% 3.22/0.99      | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1600,plain,
% 3.22/0.99      ( k2_orders_2(sK4,k2_struct_0(sK4)) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4))
% 3.22/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1599]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8936,plain,
% 3.22/0.99      ( m1_subset_1(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_4853,c_28,c_106,c_107,c_1600]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1359,plain,
% 3.22/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.22/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.22/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8942,plain,
% 3.22/0.99      ( r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top
% 3.22/0.99      | v1_xboole_0(k2_struct_0(sK4)) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_8936,c_1359]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_26,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ v5_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | sK3(X2,X1,X0) = X2 ),
% 3.22/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_552,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | sK3(X2,X1,X0) = X2
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_553,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
% 3.22/0.99      | v2_struct_0(sK4)
% 3.22/0.99      | ~ v3_orders_2(sK4)
% 3.22/0.99      | ~ v4_orders_2(sK4)
% 3.22/0.99      | ~ l1_orders_2(sK4)
% 3.22/0.99      | sK3(X1,sK4,X0) = X1 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_552]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_557,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
% 3.22/0.99      | sK3(X1,sK4,X0) = X1 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_553,c_33,c_32,c_31,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1350,plain,
% 3.22/0.99      ( sK3(X0,sK4,X1) = X0
% 3.22/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1447,plain,
% 3.22/0.99      ( sK3(X0,sK4,X1) = X0
% 3.22/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1350,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1677,plain,
% 3.22/0.99      ( sK3(sK1(a_2_1_orders_2(sK4,X0)),sK4,X0) = sK1(a_2_1_orders_2(sK4,X0))
% 3.22/0.99      | a_2_1_orders_2(sK4,X0) = k1_xboole_0
% 3.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1355,c_1447]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2196,plain,
% 3.22/0.99      ( sK3(sK1(a_2_1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(a_2_1_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1375,c_1677]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_19,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ v5_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_639,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_640,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | v2_struct_0(sK4)
% 3.22/0.99      | ~ v3_orders_2(sK4)
% 3.22/0.99      | ~ v4_orders_2(sK4)
% 3.22/0.99      | ~ l1_orders_2(sK4)
% 3.22/0.99      | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_644,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_640,c_33,c_32,c_31,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1346,plain,
% 3.22/0.99      ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
% 3.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1407,plain,
% 3.22/0.99      ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
% 3.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1346,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1613,plain,
% 3.22/0.99      ( a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k2_orders_2(sK4,k2_struct_0(sK4)) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1375,c_1407]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2206,plain,
% 3.22/0.99      ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | a_2_1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_2196,c_1613]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2207,plain,
% 3.22/0.99      ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | k2_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_2206,c_1613]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7573,plain,
% 3.22/0.99      ( sK3(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k2_orders_2(sK4,k2_struct_0(sK4))) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_2207,c_28,c_106,c_107,c_1600]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_25,plain,
% 3.22/0.99      ( r2_orders_2(X0,sK3(X1,X0,X2),X3)
% 3.22/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.22/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | ~ r2_hidden(X3,X2)
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.22/0.99      | v2_struct_0(X0)
% 3.22/0.99      | ~ v3_orders_2(X0)
% 3.22/0.99      | ~ v4_orders_2(X0)
% 3.22/0.99      | ~ v5_orders_2(X0)
% 3.22/0.99      | ~ l1_orders_2(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_478,plain,
% 3.22/0.99      ( r2_orders_2(X0,sK3(X1,X0,X2),X3)
% 3.22/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.22/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.22/0.99      | ~ r2_hidden(X3,X2)
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.22/0.99      | v2_struct_0(X0)
% 3.22/0.99      | ~ v3_orders_2(X0)
% 3.22/0.99      | ~ v4_orders_2(X0)
% 3.22/0.99      | ~ l1_orders_2(X0)
% 3.22/0.99      | sK4 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_479,plain,
% 3.22/0.99      ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
% 3.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(X2,X1)
% 3.22/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1))
% 3.22/0.99      | v2_struct_0(sK4)
% 3.22/0.99      | ~ v3_orders_2(sK4)
% 3.22/0.99      | ~ v4_orders_2(sK4)
% 3.22/0.99      | ~ l1_orders_2(sK4) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_483,plain,
% 3.22/0.99      ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
% 3.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(X2,X1)
% 3.22/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1)) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_479,c_33,c_32,c_31,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_499,plain,
% 3.22/0.99      ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2)
% 3.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(X2,X1)
% 3.22/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK4,X1)) ),
% 3.22/0.99      inference(forward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_483,c_11]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1353,plain,
% 3.22/0.99      ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2) = iProver_top
% 3.22/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.22/0.99      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1479,plain,
% 3.22/0.99      ( r2_orders_2(sK4,sK3(X0,sK4,X1),X2) = iProver_top
% 3.22/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.22/0.99      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1353,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_17,plain,
% 3.22/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 3.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.99      | ~ l1_orders_2(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_703,plain,
% 3.22/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 3.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.22/0.99      | sK4 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_704,plain,
% 3.22/0.99      ( ~ r2_orders_2(sK4,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_703]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1344,plain,
% 3.22/0.99      ( r2_orders_2(sK4,X0,X0) != iProver_top
% 3.22/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1402,plain,
% 3.22/0.99      ( r2_orders_2(sK4,X0,X0) != iProver_top
% 3.22/0.99      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1344,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1773,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) != iProver_top
% 3.22/0.99      | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top
% 3.22/0.99      | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1479,c_1402]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_27,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 3.22/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ v5_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_531,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.99      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 3.22/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 3.22/0.99      | v2_struct_0(X1)
% 3.22/0.99      | ~ v3_orders_2(X1)
% 3.22/0.99      | ~ v4_orders_2(X1)
% 3.22/0.99      | ~ l1_orders_2(X1)
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_532,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0))
% 3.22/0.99      | v2_struct_0(sK4)
% 3.22/0.99      | ~ v3_orders_2(sK4)
% 3.22/0.99      | ~ v4_orders_2(sK4)
% 3.22/0.99      | ~ l1_orders_2(sK4) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_531]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_536,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 3.22/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK4,X0)) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_532,c_33,c_32,c_31,c_29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1351,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.22/0.99      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4)) = iProver_top
% 3.22/0.99      | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1454,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) = iProver_top
% 3.22/0.99      | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_1351,c_692]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2954,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(X1,a_2_1_orders_2(sK4,X0)) != iProver_top
% 3.22/0.99      | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_1773,c_1454]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7579,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),a_2_1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_7573,c_2954]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7588,plain,
% 3.22/0.99      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 3.22/0.99      | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_7579,c_1613]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4660,plain,
% 3.22/0.99      ( ~ r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4))
% 3.22/0.99      | ~ v1_xboole_0(k2_struct_0(sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4666,plain,
% 3.22/0.99      ( r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4)) != iProver_top
% 3.22/0.99      | v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_4660]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_975,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2740,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,X1)
% 3.22/0.99      | m1_subset_1(u1_struct_0(sK4),X2)
% 3.22/0.99      | X2 != X1
% 3.22/0.99      | u1_struct_0(sK4) != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_975]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2742,plain,
% 3.22/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_xboole_0)
% 3.22/0.99      | ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
% 3.22/0.99      | u1_struct_0(sK4) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2740]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_0,plain,
% 3.22/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1364,plain,
% 3.22/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2,plain,
% 3.22/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1362,plain,
% 3.22/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2349,plain,
% 3.22/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_2,c_1362]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2484,plain,
% 3.22/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1364,c_2349]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2496,plain,
% 3.22/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.22/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2484]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2125,plain,
% 3.22/0.99      ( r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4))
% 3.22/0.99      | k1_xboole_0 = k2_struct_0(sK4) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2126,plain,
% 3.22/0.99      ( k1_xboole_0 = k2_struct_0(sK4)
% 3.22/0.99      | r2_hidden(sK1(k2_struct_0(sK4)),k2_struct_0(sK4)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1707,plain,
% 3.22/0.99      ( X0 != X1 | u1_struct_0(sK4) != X1 | u1_struct_0(sK4) = X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2015,plain,
% 3.22/0.99      ( X0 != k2_struct_0(sK4)
% 3.22/0.99      | u1_struct_0(sK4) = X0
% 3.22/0.99      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2016,plain,
% 3.22/0.99      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 3.22/0.99      | u1_struct_0(sK4) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k2_struct_0(sK4) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2015]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_12,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.99      | ~ r2_hidden(X2,X0)
% 3.22/0.99      | ~ v1_xboole_0(X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1662,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 3.22/0.99      | ~ r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | ~ v1_xboole_0(X0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1900,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1662]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1682,plain,
% 3.22/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),X0)
% 3.22/0.99      | ~ v1_xboole_0(X0)
% 3.22/0.99      | v1_xboole_0(u1_struct_0(sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1687,plain,
% 3.22/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_xboole_0)
% 3.22/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1682]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1590,plain,
% 3.22/0.99      ( r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4)))
% 3.22/0.99      | k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1591,plain,
% 3.22/0.99      ( k1_xboole_0 = k2_orders_2(sK4,k2_struct_0(sK4))
% 3.22/0.99      | r2_hidden(sK1(k2_orders_2(sK4,k2_struct_0(sK4))),k2_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_1590]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1560,plain,
% 3.22/0.99      ( m1_subset_1(k2_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.22/0.99      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_626]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6,plain,
% 3.22/0.99      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_101,plain,
% 3.22/0.99      ( m1_subset_1(k1_xboole_0,k1_xboole_0)
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(contradiction,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(minisat,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_8942,c_7588,c_4666,c_2742,c_2496,c_2126,c_2016,c_1900,
% 3.22/0.99                 c_1687,c_1591,c_1590,c_1560,c_1375,c_697,c_692,c_107,
% 3.22/0.99                 c_106,c_101,c_28]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ General
% 3.22/0.99  
% 3.22/0.99  abstr_ref_over_cycles:                  0
% 3.22/0.99  abstr_ref_under_cycles:                 0
% 3.22/0.99  gc_basic_clause_elim:                   0
% 3.22/0.99  forced_gc_time:                         0
% 3.22/0.99  parsing_time:                           0.01
% 3.22/0.99  unif_index_cands_time:                  0.
% 3.22/0.99  unif_index_add_time:                    0.
% 3.22/0.99  orderings_time:                         0.
% 3.22/0.99  out_proof_time:                         0.011
% 3.22/0.99  total_time:                             0.258
% 3.22/0.99  num_of_symbols:                         54
% 3.22/0.99  num_of_terms:                           6780
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing
% 3.22/0.99  
% 3.22/0.99  num_of_splits:                          0
% 3.22/0.99  num_of_split_atoms:                     0
% 3.22/0.99  num_of_reused_defs:                     0
% 3.22/0.99  num_eq_ax_congr_red:                    33
% 3.22/0.99  num_of_sem_filtered_clauses:            1
% 3.22/0.99  num_of_subtypes:                        0
% 3.22/0.99  monotx_restored_types:                  0
% 3.22/0.99  sat_num_of_epr_types:                   0
% 3.22/0.99  sat_num_of_non_cyclic_types:            0
% 3.22/0.99  sat_guarded_non_collapsed_types:        0
% 3.22/0.99  num_pure_diseq_elim:                    0
% 3.22/0.99  simp_replaced_by:                       0
% 3.22/0.99  res_preprocessed:                       139
% 3.22/0.99  prep_upred:                             0
% 3.22/0.99  prep_unflattend:                        25
% 3.22/0.99  smt_new_axioms:                         0
% 3.22/0.99  pred_elim_cands:                        4
% 3.22/0.99  pred_elim:                              7
% 3.22/0.99  pred_elim_cl:                           8
% 3.22/0.99  pred_elim_cycles:                       10
% 3.22/0.99  merged_defs:                            0
% 3.22/0.99  merged_defs_ncl:                        0
% 3.22/0.99  bin_hyper_res:                          0
% 3.22/0.99  prep_cycles:                            4
% 3.22/0.99  pred_elim_time:                         0.011
% 3.22/0.99  splitting_time:                         0.
% 3.22/0.99  sem_filter_time:                        0.
% 3.22/0.99  monotx_time:                            0.
% 3.22/0.99  subtype_inf_time:                       0.
% 3.22/0.99  
% 3.22/0.99  ------ Problem properties
% 3.22/0.99  
% 3.22/0.99  clauses:                                26
% 3.22/0.99  conjectures:                            1
% 3.22/0.99  epr:                                    5
% 3.22/0.99  horn:                                   20
% 3.22/0.99  ground:                                 3
% 3.22/0.99  unary:                                  7
% 3.22/0.99  binary:                                 7
% 3.22/0.99  lits:                                   61
% 3.22/0.99  lits_eq:                                10
% 3.22/0.99  fd_pure:                                0
% 3.22/0.99  fd_pseudo:                              0
% 3.22/0.99  fd_cond:                                2
% 3.22/0.99  fd_pseudo_cond:                         0
% 3.22/0.99  ac_symbols:                             0
% 3.22/0.99  
% 3.22/0.99  ------ Propositional Solver
% 3.22/0.99  
% 3.22/0.99  prop_solver_calls:                      28
% 3.22/0.99  prop_fast_solver_calls:                 1172
% 3.22/0.99  smt_solver_calls:                       0
% 3.22/0.99  smt_fast_solver_calls:                  0
% 3.22/0.99  prop_num_of_clauses:                    3127
% 3.22/0.99  prop_preprocess_simplified:             8203
% 3.22/0.99  prop_fo_subsumed:                       53
% 3.22/0.99  prop_solver_time:                       0.
% 3.22/0.99  smt_solver_time:                        0.
% 3.22/0.99  smt_fast_solver_time:                   0.
% 3.22/0.99  prop_fast_solver_time:                  0.
% 3.22/0.99  prop_unsat_core_time:                   0.
% 3.22/0.99  
% 3.22/0.99  ------ QBF
% 3.22/0.99  
% 3.22/0.99  qbf_q_res:                              0
% 3.22/0.99  qbf_num_tautologies:                    0
% 3.22/0.99  qbf_prep_cycles:                        0
% 3.22/0.99  
% 3.22/0.99  ------ BMC1
% 3.22/0.99  
% 3.22/0.99  bmc1_current_bound:                     -1
% 3.22/0.99  bmc1_last_solved_bound:                 -1
% 3.22/0.99  bmc1_unsat_core_size:                   -1
% 3.22/0.99  bmc1_unsat_core_parents_size:           -1
% 3.22/0.99  bmc1_merge_next_fun:                    0
% 3.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation
% 3.22/0.99  
% 3.22/0.99  inst_num_of_clauses:                    807
% 3.22/0.99  inst_num_in_passive:                    362
% 3.22/0.99  inst_num_in_active:                     360
% 3.22/0.99  inst_num_in_unprocessed:                85
% 3.22/0.99  inst_num_of_loops:                      490
% 3.22/0.99  inst_num_of_learning_restarts:          0
% 3.22/0.99  inst_num_moves_active_passive:          127
% 3.22/0.99  inst_lit_activity:                      0
% 3.22/0.99  inst_lit_activity_moves:                0
% 3.22/0.99  inst_num_tautologies:                   0
% 3.22/0.99  inst_num_prop_implied:                  0
% 3.22/0.99  inst_num_existing_simplified:           0
% 3.22/0.99  inst_num_eq_res_simplified:             0
% 3.22/0.99  inst_num_child_elim:                    0
% 3.22/0.99  inst_num_of_dismatching_blockings:      478
% 3.22/0.99  inst_num_of_non_proper_insts:           847
% 3.22/0.99  inst_num_of_duplicates:                 0
% 3.22/0.99  inst_inst_num_from_inst_to_res:         0
% 3.22/0.99  inst_dismatching_checking_time:         0.
% 3.22/0.99  
% 3.22/0.99  ------ Resolution
% 3.22/0.99  
% 3.22/0.99  res_num_of_clauses:                     0
% 3.22/0.99  res_num_in_passive:                     0
% 3.22/0.99  res_num_in_active:                      0
% 3.22/0.99  res_num_of_loops:                       143
% 3.22/0.99  res_forward_subset_subsumed:            57
% 3.22/0.99  res_backward_subset_subsumed:           2
% 3.22/0.99  res_forward_subsumed:                   0
% 3.22/0.99  res_backward_subsumed:                  0
% 3.22/0.99  res_forward_subsumption_resolution:     5
% 3.22/0.99  res_backward_subsumption_resolution:    0
% 3.22/0.99  res_clause_to_clause_subsumption:       708
% 3.22/0.99  res_orphan_elimination:                 0
% 3.22/0.99  res_tautology_del:                      35
% 3.22/0.99  res_num_eq_res_simplified:              0
% 3.22/0.99  res_num_sel_changes:                    0
% 3.22/0.99  res_moves_from_active_to_pass:          0
% 3.22/0.99  
% 3.22/0.99  ------ Superposition
% 3.22/0.99  
% 3.22/0.99  sup_time_total:                         0.
% 3.22/0.99  sup_time_generating:                    0.
% 3.22/0.99  sup_time_sim_full:                      0.
% 3.22/0.99  sup_time_sim_immed:                     0.
% 3.22/0.99  
% 3.22/0.99  sup_num_of_clauses:                     236
% 3.22/0.99  sup_num_in_active:                      97
% 3.22/0.99  sup_num_in_passive:                     139
% 3.22/0.99  sup_num_of_loops:                       96
% 3.22/0.99  sup_fw_superposition:                   179
% 3.22/0.99  sup_bw_superposition:                   96
% 3.22/0.99  sup_immediate_simplified:               90
% 3.22/0.99  sup_given_eliminated:                   0
% 3.22/0.99  comparisons_done:                       0
% 3.22/0.99  comparisons_avoided:                    9
% 3.22/0.99  
% 3.22/0.99  ------ Simplifications
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  sim_fw_subset_subsumed:                 35
% 3.22/0.99  sim_bw_subset_subsumed:                 1
% 3.22/0.99  sim_fw_subsumed:                        8
% 3.22/0.99  sim_bw_subsumed:                        1
% 3.22/0.99  sim_fw_subsumption_res:                 4
% 3.22/0.99  sim_bw_subsumption_res:                 0
% 3.22/0.99  sim_tautology_del:                      6
% 3.22/0.99  sim_eq_tautology_del:                   2
% 3.22/0.99  sim_eq_res_simp:                        0
% 3.22/0.99  sim_fw_demodulated:                     4
% 3.22/0.99  sim_bw_demodulated:                     0
% 3.22/0.99  sim_light_normalised:                   59
% 3.22/0.99  sim_joinable_taut:                      0
% 3.22/0.99  sim_joinable_simp:                      0
% 3.22/0.99  sim_ac_normalised:                      0
% 3.22/0.99  sim_smt_subsumption:                    0
% 3.22/0.99  
%------------------------------------------------------------------------------
