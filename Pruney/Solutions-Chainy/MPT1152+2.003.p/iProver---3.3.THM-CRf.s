%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:10 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  163 (3620 expanded)
%              Number of clauses        :   98 (1009 expanded)
%              Number of leaves         :   19 ( 784 expanded)
%              Depth                    :   22
%              Number of atoms          :  644 (17502 expanded)
%              Number of equality atoms :  180 (3187 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f57,plain,(
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

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f67,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
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

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f34])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
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

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_24,c_23,c_22,c_20])).

cnf(c_1146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_304,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_639,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_304,c_20])).

cnf(c_640,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1146,c_640])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1629,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1151])).

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
    inference(cnf_transformation,[],[f59])).

cnf(c_441,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_442,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_446,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_24,c_23,c_22,c_20])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_462,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_446,c_2])).

cnf(c_1148,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_1229,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1148,c_640])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_651,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_652,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_1140,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1169,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_640])).

cnf(c_1710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1169])).

cnf(c_2262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_1204])).

cnf(c_2587,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1629,c_2262])).

cnf(c_6,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_293,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_644,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_293,c_20])).

cnf(c_645,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_1141,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1162,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1141,c_640])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_24,c_23,c_22,c_20])).

cnf(c_1142,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1174,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1142,c_640])).

cnf(c_1386,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1162,c_1174])).

cnf(c_2593,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2587,c_1386])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1312,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1313,plain,
    ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_24,c_23,c_22,c_20])).

cnf(c_1145,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_1197,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1145,c_640])).

cnf(c_1893,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1386,c_1197])).

cnf(c_1984,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_1162])).

cnf(c_1992,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1152,c_1984])).

cnf(c_52,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_67,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_889,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1332,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_1474,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_1663,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
    | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_887,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1664,plain,
    ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_1300,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_2046,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_2808,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1992,c_20,c_19,c_52,c_67,c_1292,c_1312,c_1663,c_1664,c_2046])).

cnf(c_2815,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_2262])).

cnf(c_2827,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2815,c_1386])).

cnf(c_2813,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_1629])).

cnf(c_2835,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2813,c_1386])).

cnf(c_2986,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_19,c_1162,c_1313,c_2827,c_2835])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1540,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1149])).

cnf(c_1623,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1540])).

cnf(c_2991,plain,
    ( k2_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2986,c_1623])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_433,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_434,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_31,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_436,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_24,c_23,c_22,c_21,c_20,c_31])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_315,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11,c_4])).

cnf(c_634,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_315,c_20])).

cnf(c_635,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_1157,plain,
    ( k2_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_436,c_635,c_640])).

cnf(c_3080,plain,
    ( k2_orders_2(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2991,c_1157])).

cnf(c_3082,plain,
    ( k2_orders_2(sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2991,c_19])).

cnf(c_3088,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3080,c_3082])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.63/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/0.99  
% 2.63/0.99  ------  iProver source info
% 2.63/0.99  
% 2.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/0.99  git: non_committed_changes: false
% 2.63/0.99  git: last_make_outside_of_git: false
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     num_symb
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       true
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  ------ Parsing...
% 2.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/0.99  ------ Proving...
% 2.63/0.99  ------ Problem Properties 
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  clauses                                 17
% 2.63/0.99  conjectures                             1
% 2.63/0.99  EPR                                     1
% 2.63/0.99  Horn                                    13
% 2.63/0.99  unary                                   5
% 2.63/0.99  binary                                  3
% 2.63/0.99  lits                                    42
% 2.63/0.99  lits eq                                 7
% 2.63/0.99  fd_pure                                 0
% 2.63/0.99  fd_pseudo                               0
% 2.63/0.99  fd_cond                                 1
% 2.63/0.99  fd_pseudo_cond                          0
% 2.63/0.99  AC symbols                              0
% 2.63/0.99  
% 2.63/0.99  ------ Schedule dynamic 5 is on 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ 
% 2.63/0.99  Current options:
% 2.63/0.99  ------ 
% 2.63/0.99  
% 2.63/0.99  ------ Input Options
% 2.63/0.99  
% 2.63/0.99  --out_options                           all
% 2.63/0.99  --tptp_safe_out                         true
% 2.63/0.99  --problem_path                          ""
% 2.63/0.99  --include_path                          ""
% 2.63/0.99  --clausifier                            res/vclausify_rel
% 2.63/0.99  --clausifier_options                    --mode clausify
% 2.63/0.99  --stdin                                 false
% 2.63/0.99  --stats_out                             all
% 2.63/0.99  
% 2.63/0.99  ------ General Options
% 2.63/0.99  
% 2.63/0.99  --fof                                   false
% 2.63/0.99  --time_out_real                         305.
% 2.63/0.99  --time_out_virtual                      -1.
% 2.63/0.99  --symbol_type_check                     false
% 2.63/0.99  --clausify_out                          false
% 2.63/0.99  --sig_cnt_out                           false
% 2.63/0.99  --trig_cnt_out                          false
% 2.63/0.99  --trig_cnt_out_tolerance                1.
% 2.63/0.99  --trig_cnt_out_sk_spl                   false
% 2.63/0.99  --abstr_cl_out                          false
% 2.63/0.99  
% 2.63/0.99  ------ Global Options
% 2.63/0.99  
% 2.63/0.99  --schedule                              default
% 2.63/0.99  --add_important_lit                     false
% 2.63/0.99  --prop_solver_per_cl                    1000
% 2.63/0.99  --min_unsat_core                        false
% 2.63/0.99  --soft_assumptions                      false
% 2.63/0.99  --soft_lemma_size                       3
% 2.63/0.99  --prop_impl_unit_size                   0
% 2.63/0.99  --prop_impl_unit                        []
% 2.63/0.99  --share_sel_clauses                     true
% 2.63/0.99  --reset_solvers                         false
% 2.63/0.99  --bc_imp_inh                            [conj_cone]
% 2.63/0.99  --conj_cone_tolerance                   3.
% 2.63/0.99  --extra_neg_conj                        none
% 2.63/0.99  --large_theory_mode                     true
% 2.63/0.99  --prolific_symb_bound                   200
% 2.63/0.99  --lt_threshold                          2000
% 2.63/0.99  --clause_weak_htbl                      true
% 2.63/0.99  --gc_record_bc_elim                     false
% 2.63/0.99  
% 2.63/0.99  ------ Preprocessing Options
% 2.63/0.99  
% 2.63/0.99  --preprocessing_flag                    true
% 2.63/0.99  --time_out_prep_mult                    0.1
% 2.63/0.99  --splitting_mode                        input
% 2.63/0.99  --splitting_grd                         true
% 2.63/0.99  --splitting_cvd                         false
% 2.63/0.99  --splitting_cvd_svl                     false
% 2.63/0.99  --splitting_nvd                         32
% 2.63/0.99  --sub_typing                            true
% 2.63/0.99  --prep_gs_sim                           true
% 2.63/0.99  --prep_unflatten                        true
% 2.63/0.99  --prep_res_sim                          true
% 2.63/0.99  --prep_upred                            true
% 2.63/0.99  --prep_sem_filter                       exhaustive
% 2.63/0.99  --prep_sem_filter_out                   false
% 2.63/0.99  --pred_elim                             true
% 2.63/0.99  --res_sim_input                         true
% 2.63/0.99  --eq_ax_congr_red                       true
% 2.63/0.99  --pure_diseq_elim                       true
% 2.63/0.99  --brand_transform                       false
% 2.63/0.99  --non_eq_to_eq                          false
% 2.63/0.99  --prep_def_merge                        true
% 2.63/0.99  --prep_def_merge_prop_impl              false
% 2.63/0.99  --prep_def_merge_mbd                    true
% 2.63/0.99  --prep_def_merge_tr_red                 false
% 2.63/0.99  --prep_def_merge_tr_cl                  false
% 2.63/0.99  --smt_preprocessing                     true
% 2.63/0.99  --smt_ac_axioms                         fast
% 2.63/0.99  --preprocessed_out                      false
% 2.63/0.99  --preprocessed_stats                    false
% 2.63/0.99  
% 2.63/0.99  ------ Abstraction refinement Options
% 2.63/0.99  
% 2.63/0.99  --abstr_ref                             []
% 2.63/0.99  --abstr_ref_prep                        false
% 2.63/0.99  --abstr_ref_until_sat                   false
% 2.63/0.99  --abstr_ref_sig_restrict                funpre
% 2.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.99  --abstr_ref_under                       []
% 2.63/0.99  
% 2.63/0.99  ------ SAT Options
% 2.63/0.99  
% 2.63/0.99  --sat_mode                              false
% 2.63/0.99  --sat_fm_restart_options                ""
% 2.63/0.99  --sat_gr_def                            false
% 2.63/0.99  --sat_epr_types                         true
% 2.63/0.99  --sat_non_cyclic_types                  false
% 2.63/0.99  --sat_finite_models                     false
% 2.63/0.99  --sat_fm_lemmas                         false
% 2.63/0.99  --sat_fm_prep                           false
% 2.63/0.99  --sat_fm_uc_incr                        true
% 2.63/0.99  --sat_out_model                         small
% 2.63/0.99  --sat_out_clauses                       false
% 2.63/0.99  
% 2.63/0.99  ------ QBF Options
% 2.63/0.99  
% 2.63/0.99  --qbf_mode                              false
% 2.63/0.99  --qbf_elim_univ                         false
% 2.63/0.99  --qbf_dom_inst                          none
% 2.63/0.99  --qbf_dom_pre_inst                      false
% 2.63/0.99  --qbf_sk_in                             false
% 2.63/0.99  --qbf_pred_elim                         true
% 2.63/0.99  --qbf_split                             512
% 2.63/0.99  
% 2.63/0.99  ------ BMC1 Options
% 2.63/0.99  
% 2.63/0.99  --bmc1_incremental                      false
% 2.63/0.99  --bmc1_axioms                           reachable_all
% 2.63/0.99  --bmc1_min_bound                        0
% 2.63/0.99  --bmc1_max_bound                        -1
% 2.63/0.99  --bmc1_max_bound_default                -1
% 2.63/0.99  --bmc1_symbol_reachability              true
% 2.63/0.99  --bmc1_property_lemmas                  false
% 2.63/0.99  --bmc1_k_induction                      false
% 2.63/0.99  --bmc1_non_equiv_states                 false
% 2.63/0.99  --bmc1_deadlock                         false
% 2.63/0.99  --bmc1_ucm                              false
% 2.63/0.99  --bmc1_add_unsat_core                   none
% 2.63/0.99  --bmc1_unsat_core_children              false
% 2.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.99  --bmc1_out_stat                         full
% 2.63/0.99  --bmc1_ground_init                      false
% 2.63/0.99  --bmc1_pre_inst_next_state              false
% 2.63/0.99  --bmc1_pre_inst_state                   false
% 2.63/0.99  --bmc1_pre_inst_reach_state             false
% 2.63/0.99  --bmc1_out_unsat_core                   false
% 2.63/0.99  --bmc1_aig_witness_out                  false
% 2.63/0.99  --bmc1_verbose                          false
% 2.63/0.99  --bmc1_dump_clauses_tptp                false
% 2.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.99  --bmc1_dump_file                        -
% 2.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.99  --bmc1_ucm_extend_mode                  1
% 2.63/0.99  --bmc1_ucm_init_mode                    2
% 2.63/0.99  --bmc1_ucm_cone_mode                    none
% 2.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.99  --bmc1_ucm_relax_model                  4
% 2.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.99  --bmc1_ucm_layered_model                none
% 2.63/0.99  --bmc1_ucm_max_lemma_size               10
% 2.63/0.99  
% 2.63/0.99  ------ AIG Options
% 2.63/0.99  
% 2.63/0.99  --aig_mode                              false
% 2.63/0.99  
% 2.63/0.99  ------ Instantiation Options
% 2.63/0.99  
% 2.63/0.99  --instantiation_flag                    true
% 2.63/0.99  --inst_sos_flag                         false
% 2.63/0.99  --inst_sos_phase                        true
% 2.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.99  --inst_lit_sel_side                     none
% 2.63/0.99  --inst_solver_per_active                1400
% 2.63/0.99  --inst_solver_calls_frac                1.
% 2.63/0.99  --inst_passive_queue_type               priority_queues
% 2.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.99  --inst_passive_queues_freq              [25;2]
% 2.63/0.99  --inst_dismatching                      true
% 2.63/0.99  --inst_eager_unprocessed_to_passive     true
% 2.63/0.99  --inst_prop_sim_given                   true
% 2.63/0.99  --inst_prop_sim_new                     false
% 2.63/0.99  --inst_subs_new                         false
% 2.63/0.99  --inst_eq_res_simp                      false
% 2.63/0.99  --inst_subs_given                       false
% 2.63/0.99  --inst_orphan_elimination               true
% 2.63/0.99  --inst_learning_loop_flag               true
% 2.63/0.99  --inst_learning_start                   3000
% 2.63/0.99  --inst_learning_factor                  2
% 2.63/0.99  --inst_start_prop_sim_after_learn       3
% 2.63/0.99  --inst_sel_renew                        solver
% 2.63/0.99  --inst_lit_activity_flag                true
% 2.63/0.99  --inst_restr_to_given                   false
% 2.63/0.99  --inst_activity_threshold               500
% 2.63/0.99  --inst_out_proof                        true
% 2.63/0.99  
% 2.63/0.99  ------ Resolution Options
% 2.63/0.99  
% 2.63/0.99  --resolution_flag                       false
% 2.63/0.99  --res_lit_sel                           adaptive
% 2.63/0.99  --res_lit_sel_side                      none
% 2.63/0.99  --res_ordering                          kbo
% 2.63/0.99  --res_to_prop_solver                    active
% 2.63/0.99  --res_prop_simpl_new                    false
% 2.63/0.99  --res_prop_simpl_given                  true
% 2.63/0.99  --res_passive_queue_type                priority_queues
% 2.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.99  --res_passive_queues_freq               [15;5]
% 2.63/0.99  --res_forward_subs                      full
% 2.63/0.99  --res_backward_subs                     full
% 2.63/0.99  --res_forward_subs_resolution           true
% 2.63/0.99  --res_backward_subs_resolution          true
% 2.63/0.99  --res_orphan_elimination                true
% 2.63/0.99  --res_time_limit                        2.
% 2.63/0.99  --res_out_proof                         true
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Options
% 2.63/0.99  
% 2.63/0.99  --superposition_flag                    true
% 2.63/0.99  --sup_passive_queue_type                priority_queues
% 2.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.99  --demod_completeness_check              fast
% 2.63/0.99  --demod_use_ground                      true
% 2.63/0.99  --sup_to_prop_solver                    passive
% 2.63/0.99  --sup_prop_simpl_new                    true
% 2.63/0.99  --sup_prop_simpl_given                  true
% 2.63/0.99  --sup_fun_splitting                     false
% 2.63/0.99  --sup_smt_interval                      50000
% 2.63/0.99  
% 2.63/0.99  ------ Superposition Simplification Setup
% 2.63/0.99  
% 2.63/0.99  --sup_indices_passive                   []
% 2.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_full_bw                           [BwDemod]
% 2.63/0.99  --sup_immed_triv                        [TrivRules]
% 2.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_immed_bw_main                     []
% 2.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.99  
% 2.63/0.99  ------ Combination Options
% 2.63/0.99  
% 2.63/0.99  --comb_res_mult                         3
% 2.63/0.99  --comb_sup_mult                         2
% 2.63/0.99  --comb_inst_mult                        10
% 2.63/0.99  
% 2.63/0.99  ------ Debug Options
% 2.63/0.99  
% 2.63/0.99  --dbg_backtrace                         false
% 2.63/0.99  --dbg_dump_prop_clauses                 false
% 2.63/0.99  --dbg_dump_prop_clauses_file            -
% 2.63/0.99  --dbg_out_stat                          false
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  ------ Proving...
% 2.63/0.99  
% 2.63/0.99  
% 2.63/0.99  % SZS status Theorem for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99   Resolution empty clause
% 2.63/0.99  
% 2.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/0.99  
% 2.63/0.99  fof(f11,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f28,plain,(
% 2.63/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.63/0.99    inference(ennf_transformation,[],[f11])).
% 2.63/0.99  
% 2.63/0.99  fof(f29,plain,(
% 2.63/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.63/0.99    inference(flattening,[],[f28])).
% 2.63/0.99  
% 2.63/0.99  fof(f38,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.63/0.99    inference(nnf_transformation,[],[f29])).
% 2.63/0.99  
% 2.63/0.99  fof(f39,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.63/0.99    inference(rectify,[],[f38])).
% 2.63/0.99  
% 2.63/0.99  fof(f41,plain,(
% 2.63/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f40,plain,(
% 2.63/0.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f42,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 2.63/0.99  
% 2.63/0.99  fof(f57,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f42])).
% 2.63/0.99  
% 2.63/0.99  fof(f13,conjecture,(
% 2.63/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f14,negated_conjecture,(
% 2.63/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.63/0.99    inference(negated_conjecture,[],[f13])).
% 2.63/0.99  
% 2.63/0.99  fof(f32,plain,(
% 2.63/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f14])).
% 2.63/0.99  
% 2.63/0.99  fof(f33,plain,(
% 2.63/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.63/0.99    inference(flattening,[],[f32])).
% 2.63/0.99  
% 2.63/0.99  fof(f43,plain,(
% 2.63/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f44,plain,(
% 2.63/0.99    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f43])).
% 2.63/0.99  
% 2.63/0.99  fof(f67,plain,(
% 2.63/0.99    v5_orders_2(sK3)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f64,plain,(
% 2.63/0.99    ~v2_struct_0(sK3)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f65,plain,(
% 2.63/0.99    v3_orders_2(sK3)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f66,plain,(
% 2.63/0.99    v4_orders_2(sK3)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f68,plain,(
% 2.63/0.99    l1_orders_2(sK3)),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f10,axiom,(
% 2.63/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f27,plain,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f10])).
% 2.63/0.99  
% 2.63/0.99  fof(f56,plain,(
% 2.63/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f27])).
% 2.63/0.99  
% 2.63/0.99  fof(f6,axiom,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f22,plain,(
% 2.63/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f6])).
% 2.63/0.99  
% 2.63/0.99  fof(f50,plain,(
% 2.63/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f22])).
% 2.63/0.99  
% 2.63/0.99  fof(f2,axiom,(
% 2.63/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f16,plain,(
% 2.63/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f2])).
% 2.63/0.99  
% 2.63/0.99  fof(f17,plain,(
% 2.63/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.63/0.99    inference(flattening,[],[f16])).
% 2.63/0.99  
% 2.63/0.99  fof(f46,plain,(
% 2.63/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f17])).
% 2.63/0.99  
% 2.63/0.99  fof(f59,plain,(
% 2.63/0.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f42])).
% 2.63/0.99  
% 2.63/0.99  fof(f3,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f18,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.63/0.99    inference(ennf_transformation,[],[f3])).
% 2.63/0.99  
% 2.63/0.99  fof(f19,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.63/0.99    inference(flattening,[],[f18])).
% 2.63/0.99  
% 2.63/0.99  fof(f47,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f19])).
% 2.63/0.99  
% 2.63/0.99  fof(f8,axiom,(
% 2.63/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f24,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f8])).
% 2.63/0.99  
% 2.63/0.99  fof(f36,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.63/0.99    inference(nnf_transformation,[],[f24])).
% 2.63/0.99  
% 2.63/0.99  fof(f37,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.63/0.99    inference(flattening,[],[f36])).
% 2.63/0.99  
% 2.63/0.99  fof(f53,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f37])).
% 2.63/0.99  
% 2.63/0.99  fof(f70,plain,(
% 2.63/0.99    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.63/0.99    inference(equality_resolution,[],[f53])).
% 2.63/0.99  
% 2.63/0.99  fof(f7,axiom,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f23,plain,(
% 2.63/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f7])).
% 2.63/0.99  
% 2.63/0.99  fof(f51,plain,(
% 2.63/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f23])).
% 2.63/0.99  
% 2.63/0.99  fof(f9,axiom,(
% 2.63/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f25,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f9])).
% 2.63/0.99  
% 2.63/0.99  fof(f26,plain,(
% 2.63/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.63/0.99    inference(flattening,[],[f25])).
% 2.63/0.99  
% 2.63/0.99  fof(f55,plain,(
% 2.63/0.99    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f26])).
% 2.63/0.99  
% 2.63/0.99  fof(f69,plain,(
% 2.63/0.99    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 2.63/0.99    inference(cnf_transformation,[],[f44])).
% 2.63/0.99  
% 2.63/0.99  fof(f1,axiom,(
% 2.63/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f15,plain,(
% 2.63/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.63/0.99    inference(ennf_transformation,[],[f1])).
% 2.63/0.99  
% 2.63/0.99  fof(f34,plain,(
% 2.63/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.63/0.99    introduced(choice_axiom,[])).
% 2.63/0.99  
% 2.63/0.99  fof(f35,plain,(
% 2.63/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f34])).
% 2.63/0.99  
% 2.63/0.99  fof(f45,plain,(
% 2.63/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.63/0.99    inference(cnf_transformation,[],[f35])).
% 2.63/0.99  
% 2.63/0.99  fof(f58,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f42])).
% 2.63/0.99  
% 2.63/0.99  fof(f4,axiom,(
% 2.63/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f20,plain,(
% 2.63/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.63/0.99    inference(ennf_transformation,[],[f4])).
% 2.63/0.99  
% 2.63/0.99  fof(f48,plain,(
% 2.63/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f20])).
% 2.63/0.99  
% 2.63/0.99  fof(f12,axiom,(
% 2.63/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f30,plain,(
% 2.63/0.99    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.63/0.99    inference(ennf_transformation,[],[f12])).
% 2.63/0.99  
% 2.63/0.99  fof(f31,plain,(
% 2.63/0.99    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.63/0.99    inference(flattening,[],[f30])).
% 2.63/0.99  
% 2.63/0.99  fof(f63,plain,(
% 2.63/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f31])).
% 2.63/0.99  
% 2.63/0.99  fof(f5,axiom,(
% 2.63/0.99    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 2.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/0.99  
% 2.63/0.99  fof(f21,plain,(
% 2.63/0.99    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.63/0.99    inference(ennf_transformation,[],[f5])).
% 2.63/0.99  
% 2.63/0.99  fof(f49,plain,(
% 2.63/0.99    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.63/0.99    inference(cnf_transformation,[],[f21])).
% 2.63/0.99  
% 2.63/0.99  cnf(c_17,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.63/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ v5_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_21,negated_conjecture,
% 2.63/0.99      ( v5_orders_2(sK3) ),
% 2.63/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_494,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.63/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1)
% 2.63/0.99      | sK3 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_495,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.63/0.99      | v2_struct_0(sK3)
% 2.63/0.99      | ~ v3_orders_2(sK3)
% 2.63/0.99      | ~ v4_orders_2(sK3)
% 2.63/0.99      | ~ l1_orders_2(sK3) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_24,negated_conjecture,
% 2.63/0.99      ( ~ v2_struct_0(sK3) ),
% 2.63/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_23,negated_conjecture,
% 2.63/0.99      ( v3_orders_2(sK3) ),
% 2.63/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_22,negated_conjecture,
% 2.63/0.99      ( v4_orders_2(sK3) ),
% 2.63/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_20,negated_conjecture,
% 2.63/0.99      ( l1_orders_2(sK3) ),
% 2.63/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_499,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_495,c_24,c_23,c_22,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1146,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.63/0.99      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 2.63/0.99      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_11,plain,
% 2.63/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_5,plain,
% 2.63/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_304,plain,
% 2.63/0.99      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.63/0.99      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_639,plain,
% 2.63/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_304,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_640,plain,
% 2.63/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1204,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.63/0.99      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1146,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.63/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1151,plain,
% 2.63/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.63/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.63/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1629,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.63/0.99      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1204,c_1151]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_15,plain,
% 2.63/0.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.63/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.63/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ r2_hidden(X3,X2)
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.63/0.99      | v2_struct_0(X0)
% 2.63/0.99      | ~ v3_orders_2(X0)
% 2.63/0.99      | ~ v4_orders_2(X0)
% 2.63/0.99      | ~ v5_orders_2(X0)
% 2.63/0.99      | ~ l1_orders_2(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_441,plain,
% 2.63/0.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.63/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.63/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ r2_hidden(X3,X2)
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.63/0.99      | v2_struct_0(X0)
% 2.63/0.99      | ~ v3_orders_2(X0)
% 2.63/0.99      | ~ v4_orders_2(X0)
% 2.63/0.99      | ~ l1_orders_2(X0)
% 2.63/0.99      | sK3 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_442,plain,
% 2.63/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.63/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X2,X1)
% 2.63/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 2.63/0.99      | v2_struct_0(sK3)
% 2.63/0.99      | ~ v3_orders_2(sK3)
% 2.63/0.99      | ~ v4_orders_2(sK3)
% 2.63/0.99      | ~ l1_orders_2(sK3) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_441]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_446,plain,
% 2.63/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.63/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X2,X1)
% 2.63/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_442,c_24,c_23,c_22,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2,plain,
% 2.63/0.99      ( m1_subset_1(X0,X1)
% 2.63/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.63/0.99      | ~ r2_hidden(X0,X2) ),
% 2.63/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_462,plain,
% 2.63/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.63/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X2,X1)
% 2.63/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 2.63/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_446,c_2]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1148,plain,
% 2.63/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.63/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X2,X1) != iProver_top
% 2.63/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1229,plain,
% 2.63/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.63/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X2,X1) != iProver_top
% 2.63/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1148,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_8,plain,
% 2.63/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 2.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.63/0.99      | ~ l1_orders_2(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_651,plain,
% 2.63/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 2.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.63/0.99      | sK3 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_652,plain,
% 2.63/0.99      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_651]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1140,plain,
% 2.63/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1169,plain,
% 2.63/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.63/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1140,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1710,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 2.63/0.99      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.63/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1229,c_1169]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2262,plain,
% 2.63/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.63/0.99      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1710,c_1204]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2587,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1629,c_2262]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_6,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ l1_struct_0(X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_293,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.63/0.99      | ~ l1_orders_2(X0) ),
% 2.63/0.99      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_644,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK3 != X0 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_293,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_645,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_644]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1141,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1162,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1141,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_10,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ v5_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1)
% 2.63/0.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 2.63/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_584,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1)
% 2.63/0.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 2.63/0.99      | sK3 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_585,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | v2_struct_0(sK3)
% 2.63/0.99      | ~ v3_orders_2(sK3)
% 2.63/0.99      | ~ v4_orders_2(sK3)
% 2.63/0.99      | ~ l1_orders_2(sK3)
% 2.63/0.99      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_589,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_585,c_24,c_23,c_22,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1142,plain,
% 2.63/0.99      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1174,plain,
% 2.63/0.99      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.63/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1142,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1386,plain,
% 2.63/0.99      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1162,c_1174]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2593,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_2587,c_1386]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_19,negated_conjecture,
% 2.63/0.99      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.63/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_0,plain,
% 2.63/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.63/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1312,plain,
% 2.63/0.99      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1313,plain,
% 2.63/0.99      ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 2.63/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1152,plain,
% 2.63/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_16,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ v5_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1)
% 2.63/0.99      | sK2(X2,X1,X0) = X2 ),
% 2.63/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_515,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.63/0.99      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.63/0.99      | v2_struct_0(X1)
% 2.63/0.99      | ~ v3_orders_2(X1)
% 2.63/0.99      | ~ v4_orders_2(X1)
% 2.63/0.99      | ~ l1_orders_2(X1)
% 2.63/0.99      | sK2(X2,X1,X0) = X2
% 2.63/0.99      | sK3 != X1 ),
% 2.63/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_516,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.63/0.99      | v2_struct_0(sK3)
% 2.63/0.99      | ~ v3_orders_2(sK3)
% 2.63/0.99      | ~ v4_orders_2(sK3)
% 2.63/0.99      | ~ l1_orders_2(sK3)
% 2.63/0.99      | sK2(X1,sK3,X0) = X1 ),
% 2.63/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_520,plain,
% 2.63/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.63/0.99      | sK2(X1,sK3,X0) = X1 ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_516,c_24,c_23,c_22,c_20]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1145,plain,
% 2.63/0.99      ( sK2(X0,sK3,X1) = X0
% 2.63/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.63/0.99      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1197,plain,
% 2.63/0.99      ( sK2(X0,sK3,X1) = X0
% 2.63/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.63/0.99      inference(light_normalisation,[status(thm)],[c_1145,c_640]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1893,plain,
% 2.63/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.63/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1386,c_1197]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1984,plain,
% 2.63/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.63/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.63/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1893,c_1162]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1992,plain,
% 2.63/0.99      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_1152,c_1984]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_52,plain,
% 2.63/0.99      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_67,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ l1_struct_0(sK3) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1292,plain,
% 2.63/0.99      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_589]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_889,plain,
% 2.63/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.63/0.99      theory(equality) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1332,plain,
% 2.63/0.99      ( r2_hidden(X0,X1)
% 2.63/0.99      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
% 2.63/0.99      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_889]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1474,plain,
% 2.63/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_1332]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1663,plain,
% 2.63/0.99      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
% 2.63/0.99      | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_1474]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_887,plain,( X0 = X0 ),theory(equality) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1664,plain,
% 2.63/0.99      ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_887]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_1300,plain,
% 2.63/0.99      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_520]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2046,plain,
% 2.63/0.99      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.63/0.99      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.63/0.99      | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.63/0.99      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2808,plain,
% 2.63/0.99      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.63/0.99      inference(global_propositional_subsumption,
% 2.63/0.99                [status(thm)],
% 2.63/0.99                [c_1992,c_20,c_19,c_52,c_67,c_1292,c_1312,c_1663,c_1664,c_2046]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2815,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.63/0.99      inference(superposition,[status(thm)],[c_2808,c_2262]) ).
% 2.63/0.99  
% 2.63/0.99  cnf(c_2827,plain,
% 2.63/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_2815,c_1386]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2813,plain,
% 2.63/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/1.00      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/1.00      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 2.63/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2808,c_1629]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2835,plain,
% 2.63/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.63/1.00      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.63/1.00      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 2.63/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_2813,c_1386]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2986,plain,
% 2.63/1.00      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_2593,c_19,c_1162,c_1313,c_2827,c_2835]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.63/1.00      | ~ r2_hidden(X2,X0)
% 2.63/1.00      | ~ v1_xboole_0(X1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1149,plain,
% 2.63/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.63/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.63/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1540,plain,
% 2.63/1.00      ( r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 2.63/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1162,c_1149]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1623,plain,
% 2.63/1.00      ( k2_struct_0(sK3) = k1_xboole_0
% 2.63/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1152,c_1540]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2991,plain,
% 2.63/1.00      ( k2_struct_0(sK3) = k1_xboole_0 ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_2986,c_1623]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_18,plain,
% 2.63/1.00      ( v2_struct_0(X0)
% 2.63/1.00      | ~ v3_orders_2(X0)
% 2.63/1.00      | ~ v4_orders_2(X0)
% 2.63/1.00      | ~ v5_orders_2(X0)
% 2.63/1.00      | ~ l1_orders_2(X0)
% 2.63/1.00      | k2_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_433,plain,
% 2.63/1.00      ( v2_struct_0(X0)
% 2.63/1.00      | ~ v3_orders_2(X0)
% 2.63/1.00      | ~ v4_orders_2(X0)
% 2.63/1.00      | ~ l1_orders_2(X0)
% 2.63/1.00      | k2_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
% 2.63/1.00      | sK3 != X0 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_434,plain,
% 2.63/1.00      ( v2_struct_0(sK3)
% 2.63/1.00      | ~ v3_orders_2(sK3)
% 2.63/1.00      | ~ v4_orders_2(sK3)
% 2.63/1.00      | ~ l1_orders_2(sK3)
% 2.63/1.00      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_433]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_31,plain,
% 2.63/1.00      ( v2_struct_0(sK3)
% 2.63/1.00      | ~ v3_orders_2(sK3)
% 2.63/1.00      | ~ v4_orders_2(sK3)
% 2.63/1.00      | ~ v5_orders_2(sK3)
% 2.63/1.00      | ~ l1_orders_2(sK3)
% 2.63/1.00      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.63/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_436,plain,
% 2.63/1.00      ( k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_434,c_24,c_23,c_22,c_21,c_20,c_31]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_4,plain,
% 2.63/1.00      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 2.63/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_315,plain,
% 2.63/1.00      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 2.63/1.00      inference(resolution,[status(thm)],[c_11,c_4]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_634,plain,
% 2.63/1.00      ( k1_struct_0(X0) = k1_xboole_0 | sK3 != X0 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_315,c_20]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_635,plain,
% 2.63/1.00      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_634]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1157,plain,
% 2.63/1.00      ( k2_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_436,c_635,c_640]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3080,plain,
% 2.63/1.00      ( k2_orders_2(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_2991,c_1157]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3082,plain,
% 2.63/1.00      ( k2_orders_2(sK3,k1_xboole_0) != k1_xboole_0 ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_2991,c_19]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_3088,plain,
% 2.63/1.00      ( $false ),
% 2.63/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3080,c_3082]) ).
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  ------                               Statistics
% 2.63/1.00  
% 2.63/1.00  ------ General
% 2.63/1.00  
% 2.63/1.00  abstr_ref_over_cycles:                  0
% 2.63/1.00  abstr_ref_under_cycles:                 0
% 2.63/1.00  gc_basic_clause_elim:                   0
% 2.63/1.00  forced_gc_time:                         0
% 2.63/1.00  parsing_time:                           0.013
% 2.63/1.00  unif_index_cands_time:                  0.
% 2.63/1.00  unif_index_add_time:                    0.
% 2.63/1.00  orderings_time:                         0.
% 2.63/1.00  out_proof_time:                         0.01
% 2.63/1.00  total_time:                             0.131
% 2.63/1.00  num_of_symbols:                         53
% 2.63/1.00  num_of_terms:                           2666
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing
% 2.63/1.00  
% 2.63/1.00  num_of_splits:                          0
% 2.63/1.00  num_of_split_atoms:                     0
% 2.63/1.00  num_of_reused_defs:                     0
% 2.63/1.00  num_eq_ax_congr_red:                    31
% 2.63/1.00  num_of_sem_filtered_clauses:            1
% 2.63/1.00  num_of_subtypes:                        0
% 2.63/1.00  monotx_restored_types:                  0
% 2.63/1.00  sat_num_of_epr_types:                   0
% 2.63/1.00  sat_num_of_non_cyclic_types:            0
% 2.63/1.00  sat_guarded_non_collapsed_types:        0
% 2.63/1.00  num_pure_diseq_elim:                    0
% 2.63/1.00  simp_replaced_by:                       0
% 2.63/1.00  res_preprocessed:                       103
% 2.63/1.00  prep_upred:                             0
% 2.63/1.00  prep_unflattend:                        26
% 2.63/1.00  smt_new_axioms:                         0
% 2.63/1.00  pred_elim_cands:                        4
% 2.63/1.00  pred_elim:                              7
% 2.63/1.00  pred_elim_cl:                           8
% 2.63/1.00  pred_elim_cycles:                       12
% 2.63/1.00  merged_defs:                            0
% 2.63/1.00  merged_defs_ncl:                        0
% 2.63/1.00  bin_hyper_res:                          0
% 2.63/1.00  prep_cycles:                            4
% 2.63/1.00  pred_elim_time:                         0.009
% 2.63/1.00  splitting_time:                         0.
% 2.63/1.00  sem_filter_time:                        0.
% 2.63/1.00  monotx_time:                            0.
% 2.63/1.00  subtype_inf_time:                       0.
% 2.63/1.00  
% 2.63/1.00  ------ Problem properties
% 2.63/1.00  
% 2.63/1.00  clauses:                                17
% 2.63/1.00  conjectures:                            1
% 2.63/1.00  epr:                                    1
% 2.63/1.00  horn:                                   13
% 2.63/1.00  ground:                                 5
% 2.63/1.00  unary:                                  5
% 2.63/1.00  binary:                                 3
% 2.63/1.00  lits:                                   42
% 2.63/1.00  lits_eq:                                7
% 2.63/1.00  fd_pure:                                0
% 2.63/1.00  fd_pseudo:                              0
% 2.63/1.00  fd_cond:                                1
% 2.63/1.00  fd_pseudo_cond:                         0
% 2.63/1.00  ac_symbols:                             0
% 2.63/1.00  
% 2.63/1.00  ------ Propositional Solver
% 2.63/1.00  
% 2.63/1.00  prop_solver_calls:                      27
% 2.63/1.00  prop_fast_solver_calls:                 891
% 2.63/1.00  smt_solver_calls:                       0
% 2.63/1.00  smt_fast_solver_calls:                  0
% 2.63/1.00  prop_num_of_clauses:                    1077
% 2.63/1.00  prop_preprocess_simplified:             3871
% 2.63/1.00  prop_fo_subsumed:                       43
% 2.63/1.00  prop_solver_time:                       0.
% 2.63/1.00  smt_solver_time:                        0.
% 2.63/1.00  smt_fast_solver_time:                   0.
% 2.63/1.00  prop_fast_solver_time:                  0.
% 2.63/1.00  prop_unsat_core_time:                   0.
% 2.63/1.00  
% 2.63/1.00  ------ QBF
% 2.63/1.00  
% 2.63/1.00  qbf_q_res:                              0
% 2.63/1.00  qbf_num_tautologies:                    0
% 2.63/1.00  qbf_prep_cycles:                        0
% 2.63/1.00  
% 2.63/1.00  ------ BMC1
% 2.63/1.00  
% 2.63/1.00  bmc1_current_bound:                     -1
% 2.63/1.00  bmc1_last_solved_bound:                 -1
% 2.63/1.00  bmc1_unsat_core_size:                   -1
% 2.63/1.00  bmc1_unsat_core_parents_size:           -1
% 2.63/1.00  bmc1_merge_next_fun:                    0
% 2.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation
% 2.63/1.00  
% 2.63/1.00  inst_num_of_clauses:                    331
% 2.63/1.00  inst_num_in_passive:                    76
% 2.63/1.00  inst_num_in_active:                     185
% 2.63/1.00  inst_num_in_unprocessed:                70
% 2.63/1.00  inst_num_of_loops:                      200
% 2.63/1.00  inst_num_of_learning_restarts:          0
% 2.63/1.00  inst_num_moves_active_passive:          11
% 2.63/1.00  inst_lit_activity:                      0
% 2.63/1.00  inst_lit_activity_moves:                0
% 2.63/1.00  inst_num_tautologies:                   0
% 2.63/1.00  inst_num_prop_implied:                  0
% 2.63/1.00  inst_num_existing_simplified:           0
% 2.63/1.00  inst_num_eq_res_simplified:             0
% 2.63/1.00  inst_num_child_elim:                    0
% 2.63/1.00  inst_num_of_dismatching_blockings:      39
% 2.63/1.00  inst_num_of_non_proper_insts:           277
% 2.63/1.00  inst_num_of_duplicates:                 0
% 2.63/1.00  inst_inst_num_from_inst_to_res:         0
% 2.63/1.00  inst_dismatching_checking_time:         0.
% 2.63/1.00  
% 2.63/1.00  ------ Resolution
% 2.63/1.00  
% 2.63/1.00  res_num_of_clauses:                     0
% 2.63/1.00  res_num_in_passive:                     0
% 2.63/1.00  res_num_in_active:                      0
% 2.63/1.00  res_num_of_loops:                       107
% 2.63/1.00  res_forward_subset_subsumed:            61
% 2.63/1.00  res_backward_subset_subsumed:           0
% 2.63/1.00  res_forward_subsumed:                   0
% 2.63/1.00  res_backward_subsumed:                  0
% 2.63/1.00  res_forward_subsumption_resolution:     5
% 2.63/1.00  res_backward_subsumption_resolution:    0
% 2.63/1.00  res_clause_to_clause_subsumption:       135
% 2.63/1.00  res_orphan_elimination:                 0
% 2.63/1.00  res_tautology_del:                      35
% 2.63/1.00  res_num_eq_res_simplified:              0
% 2.63/1.00  res_num_sel_changes:                    0
% 2.63/1.00  res_moves_from_active_to_pass:          0
% 2.63/1.00  
% 2.63/1.00  ------ Superposition
% 2.63/1.00  
% 2.63/1.00  sup_time_total:                         0.
% 2.63/1.00  sup_time_generating:                    0.
% 2.63/1.00  sup_time_sim_full:                      0.
% 2.63/1.00  sup_time_sim_immed:                     0.
% 2.63/1.00  
% 2.63/1.00  sup_num_of_clauses:                     20
% 2.63/1.00  sup_num_in_active:                      5
% 2.63/1.00  sup_num_in_passive:                     15
% 2.63/1.00  sup_num_of_loops:                       38
% 2.63/1.00  sup_fw_superposition:                   21
% 2.63/1.00  sup_bw_superposition:                   25
% 2.63/1.00  sup_immediate_simplified:               14
% 2.63/1.00  sup_given_eliminated:                   0
% 2.63/1.00  comparisons_done:                       0
% 2.63/1.00  comparisons_avoided:                    6
% 2.63/1.00  
% 2.63/1.00  ------ Simplifications
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  sim_fw_subset_subsumed:                 2
% 2.63/1.00  sim_bw_subset_subsumed:                 3
% 2.63/1.00  sim_fw_subsumed:                        1
% 2.63/1.00  sim_bw_subsumed:                        0
% 2.63/1.00  sim_fw_subsumption_res:                 2
% 2.63/1.00  sim_bw_subsumption_res:                 0
% 2.63/1.00  sim_tautology_del:                      3
% 2.63/1.00  sim_eq_tautology_del:                   1
% 2.63/1.00  sim_eq_res_simp:                        0
% 2.63/1.00  sim_fw_demodulated:                     1
% 2.63/1.00  sim_bw_demodulated:                     30
% 2.63/1.00  sim_light_normalised:                   23
% 2.63/1.00  sim_joinable_taut:                      0
% 2.63/1.00  sim_joinable_simp:                      0
% 2.63/1.00  sim_ac_normalised:                      0
% 2.63/1.00  sim_smt_subsumption:                    0
% 2.63/1.00  
%------------------------------------------------------------------------------
