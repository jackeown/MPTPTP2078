%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 263 expanded)
%              Number of clauses        :   57 (  82 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  459 (1272 expanded)
%              Number of equality atoms :  151 ( 286 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).

fof(f54,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f51])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_630,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_613,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_629,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_625,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1932,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_625])).

cnf(c_2843,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
    | v2_struct_0(sK3) = iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_1932])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_921,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_924,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_977,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_980,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_2846,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2843,c_21,c_20,c_19,c_18,c_17,c_924,c_980])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_632,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_621,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1333,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_627])).

cnf(c_2186,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_1333])).

cnf(c_9102,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2186,c_629])).

cnf(c_9106,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_9102])).

cnf(c_9118,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_9106])).

cnf(c_22,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_26,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9297,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9118,c_22,c_23,c_24,c_25,c_26])).

cnf(c_9298,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9297])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_631,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9305,plain,
    ( k2_orders_2(sK3,k1_xboole_0) = X0
    | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK0(X0,k2_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9298,c_631])).

cnf(c_9581,plain,
    ( k2_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
    | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_630,c_9305])).

cnf(c_616,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_623,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1082,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_623])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_626,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1354,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1082,c_626])).

cnf(c_16,negated_conjecture,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1427,plain,
    ( k2_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_1354,c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_922,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_927,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_929,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_923,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_925,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9581,c_1427,c_929,c_925,c_26,c_25,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.41/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/1.00  
% 3.41/1.00  ------  iProver source info
% 3.41/1.00  
% 3.41/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.41/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/1.00  git: non_committed_changes: false
% 3.41/1.00  git: last_make_outside_of_git: false
% 3.41/1.00  
% 3.41/1.00  ------ 
% 3.41/1.00  ------ Parsing...
% 3.41/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.00  ------ Proving...
% 3.41/1.00  ------ Problem Properties 
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  clauses                                 22
% 3.41/1.00  conjectures                             6
% 3.41/1.00  EPR                                     7
% 3.41/1.00  Horn                                    13
% 3.41/1.00  unary                                   8
% 3.41/1.00  binary                                  2
% 3.41/1.00  lits                                    91
% 3.41/1.00  lits eq                                 6
% 3.41/1.00  fd_pure                                 0
% 3.41/1.00  fd_pseudo                               0
% 3.41/1.00  fd_cond                                 0
% 3.41/1.00  fd_pseudo_cond                          2
% 3.41/1.00  AC symbols                              0
% 3.41/1.00  
% 3.41/1.00  ------ Input Options Time Limit: Unbounded
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  ------ 
% 3.41/1.00  Current options:
% 3.41/1.00  ------ 
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  ------ Proving...
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  % SZS status Theorem for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  fof(f2,axiom,(
% 3.41/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f13,plain,(
% 3.41/1.00    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/1.00    inference(ennf_transformation,[],[f2])).
% 3.41/1.00  
% 3.41/1.00  fof(f14,plain,(
% 3.41/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/1.00    inference(flattening,[],[f13])).
% 3.41/1.00  
% 3.41/1.00  fof(f28,plain,(
% 3.41/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f29,plain,(
% 3.41/1.00    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).
% 3.41/1.00  
% 3.41/1.00  fof(f38,plain,(
% 3.41/1.00    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f29])).
% 3.41/1.00  
% 3.41/1.00  fof(f11,conjecture,(
% 3.41/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f12,negated_conjecture,(
% 3.41/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 3.41/1.00    inference(negated_conjecture,[],[f11])).
% 3.41/1.00  
% 3.41/1.00  fof(f26,plain,(
% 3.41/1.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.41/1.00    inference(ennf_transformation,[],[f12])).
% 3.41/1.00  
% 3.41/1.00  fof(f27,plain,(
% 3.41/1.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.41/1.00    inference(flattening,[],[f26])).
% 3.41/1.00  
% 3.41/1.00  fof(f35,plain,(
% 3.41/1.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f36,plain,(
% 3.41/1.00    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).
% 3.41/1.00  
% 3.41/1.00  fof(f54,plain,(
% 3.41/1.00    v3_orders_2(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f3,axiom,(
% 3.41/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f40,plain,(
% 3.41/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f3])).
% 3.41/1.00  
% 3.41/1.00  fof(f7,axiom,(
% 3.41/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f19,plain,(
% 3.41/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.41/1.00    inference(ennf_transformation,[],[f7])).
% 3.41/1.00  
% 3.41/1.00  fof(f20,plain,(
% 3.41/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.41/1.00    inference(flattening,[],[f19])).
% 3.41/1.00  
% 3.41/1.00  fof(f44,plain,(
% 3.41/1.00    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f20])).
% 3.41/1.00  
% 3.41/1.00  fof(f53,plain,(
% 3.41/1.00    ~v2_struct_0(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f55,plain,(
% 3.41/1.00    v4_orders_2(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f56,plain,(
% 3.41/1.00    v5_orders_2(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f57,plain,(
% 3.41/1.00    l1_orders_2(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f1,axiom,(
% 3.41/1.00    v1_xboole_0(k1_xboole_0)),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f37,plain,(
% 3.41/1.00    v1_xboole_0(k1_xboole_0)),
% 3.41/1.00    inference(cnf_transformation,[],[f1])).
% 3.41/1.00  
% 3.41/1.00  fof(f10,axiom,(
% 3.41/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f24,plain,(
% 3.41/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.41/1.00    inference(ennf_transformation,[],[f10])).
% 3.41/1.00  
% 3.41/1.00  fof(f25,plain,(
% 3.41/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.41/1.00    inference(flattening,[],[f24])).
% 3.41/1.00  
% 3.41/1.00  fof(f30,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.41/1.00    inference(nnf_transformation,[],[f25])).
% 3.41/1.00  
% 3.41/1.00  fof(f31,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.41/1.00    inference(rectify,[],[f30])).
% 3.41/1.00  
% 3.41/1.00  fof(f33,plain,(
% 3.41/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f32,plain,(
% 3.41/1.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f34,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 3.41/1.00  
% 3.41/1.00  fof(f51,plain,(
% 3.41/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f34])).
% 3.41/1.00  
% 3.41/1.00  fof(f60,plain,(
% 3.41/1.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.41/1.00    inference(equality_resolution,[],[f51])).
% 3.41/1.00  
% 3.41/1.00  fof(f5,axiom,(
% 3.41/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f17,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.41/1.00    inference(ennf_transformation,[],[f5])).
% 3.41/1.00  
% 3.41/1.00  fof(f42,plain,(
% 3.41/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f17])).
% 3.41/1.00  
% 3.41/1.00  fof(f39,plain,(
% 3.41/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f29])).
% 3.41/1.00  
% 3.41/1.00  fof(f9,axiom,(
% 3.41/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f23,plain,(
% 3.41/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f9])).
% 3.41/1.00  
% 3.41/1.00  fof(f46,plain,(
% 3.41/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f23])).
% 3.41/1.00  
% 3.41/1.00  fof(f6,axiom,(
% 3.41/1.00    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f18,plain,(
% 3.41/1.00    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f6])).
% 3.41/1.00  
% 3.41/1.00  fof(f43,plain,(
% 3.41/1.00    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f18])).
% 3.41/1.00  
% 3.41/1.00  fof(f58,plain,(
% 3.41/1.00    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))),
% 3.41/1.00    inference(cnf_transformation,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f8,axiom,(
% 3.41/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.41/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f21,plain,(
% 3.41/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.41/1.00    inference(ennf_transformation,[],[f8])).
% 3.41/1.00  
% 3.41/1.00  fof(f22,plain,(
% 3.41/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.41/1.00    inference(flattening,[],[f21])).
% 3.41/1.00  
% 3.41/1.00  fof(f45,plain,(
% 3.41/1.00    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f22])).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/1.00      | m1_subset_1(sK0(X1,X0),X1)
% 3.41/1.00      | X0 = X1 ),
% 3.41/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_630,plain,
% 3.41/1.00      ( X0 = X1
% 3.41/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.00      | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_20,negated_conjecture,
% 3.41/1.00      ( v3_orders_2(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_613,plain,
% 3.41/1.00      ( v3_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_629,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_7,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/1.00      | v2_struct_0(X1)
% 3.41/1.00      | ~ v3_orders_2(X1)
% 3.41/1.00      | ~ v4_orders_2(X1)
% 3.41/1.00      | ~ v5_orders_2(X1)
% 3.41/1.00      | ~ l1_orders_2(X1)
% 3.41/1.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_625,plain,
% 3.41/1.00      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 3.41/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.41/1.00      | v2_struct_0(X0) = iProver_top
% 3.41/1.00      | v3_orders_2(X0) != iProver_top
% 3.41/1.00      | v4_orders_2(X0) != iProver_top
% 3.41/1.00      | v5_orders_2(X0) != iProver_top
% 3.41/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1932,plain,
% 3.41/1.00      ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
% 3.41/1.00      | v2_struct_0(X0) = iProver_top
% 3.41/1.00      | v3_orders_2(X0) != iProver_top
% 3.41/1.00      | v4_orders_2(X0) != iProver_top
% 3.41/1.00      | v5_orders_2(X0) != iProver_top
% 3.41/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_629,c_625]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2843,plain,
% 3.41/1.00      ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
% 3.41/1.00      | v2_struct_0(sK3) = iProver_top
% 3.41/1.00      | v4_orders_2(sK3) != iProver_top
% 3.41/1.00      | v5_orders_2(sK3) != iProver_top
% 3.41/1.00      | l1_orders_2(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_613,c_1932]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_21,negated_conjecture,
% 3.41/1.00      ( ~ v2_struct_0(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_19,negated_conjecture,
% 3.41/1.00      ( v4_orders_2(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_18,negated_conjecture,
% 3.41/1.00      ( v5_orders_2(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_17,negated_conjecture,
% 3.41/1.00      ( l1_orders_2(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_921,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_924,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_921]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_977,plain,
% 3.41/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.41/1.00      | v2_struct_0(X0)
% 3.41/1.00      | ~ v3_orders_2(X0)
% 3.41/1.00      | ~ v4_orders_2(X0)
% 3.41/1.00      | ~ v5_orders_2(X0)
% 3.41/1.00      | ~ l1_orders_2(X0)
% 3.41/1.00      | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_980,plain,
% 3.41/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.41/1.00      | v2_struct_0(sK3)
% 3.41/1.00      | ~ v3_orders_2(sK3)
% 3.41/1.00      | ~ v4_orders_2(sK3)
% 3.41/1.00      | ~ v5_orders_2(sK3)
% 3.41/1.00      | ~ l1_orders_2(sK3)
% 3.41/1.00      | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_977]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2846,plain,
% 3.41/1.00      ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_2843,c_21,c_20,c_19,c_18,c_17,c_924,c_980]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_0,plain,
% 3.41/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_632,plain,
% 3.41/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_11,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/1.00      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.41/1.00      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.41/1.00      | v2_struct_0(X1)
% 3.41/1.00      | ~ v3_orders_2(X1)
% 3.41/1.00      | ~ v4_orders_2(X1)
% 3.41/1.00      | ~ v5_orders_2(X1)
% 3.41/1.00      | ~ l1_orders_2(X1) ),
% 3.41/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_621,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.41/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.41/1.00      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 3.41/1.00      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 3.41/1.00      | v2_struct_0(X1) = iProver_top
% 3.41/1.00      | v3_orders_2(X1) != iProver_top
% 3.41/1.00      | v4_orders_2(X1) != iProver_top
% 3.41/1.00      | v5_orders_2(X1) != iProver_top
% 3.41/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_5,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/1.00      | ~ r2_hidden(X2,X0)
% 3.41/1.00      | ~ v1_xboole_0(X1) ),
% 3.41/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_627,plain,
% 3.41/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.41/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1333,plain,
% 3.41/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.41/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_629,c_627]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2186,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.41/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.41/1.00      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 3.41/1.00      | v2_struct_0(X1) = iProver_top
% 3.41/1.00      | v3_orders_2(X1) != iProver_top
% 3.41/1.00      | v4_orders_2(X1) != iProver_top
% 3.41/1.00      | v5_orders_2(X1) != iProver_top
% 3.41/1.00      | l1_orders_2(X1) != iProver_top
% 3.41/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_621,c_1333]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9102,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.41/1.00      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 3.41/1.00      | v2_struct_0(X1) = iProver_top
% 3.41/1.00      | v3_orders_2(X1) != iProver_top
% 3.41/1.00      | v4_orders_2(X1) != iProver_top
% 3.41/1.00      | v5_orders_2(X1) != iProver_top
% 3.41/1.00      | l1_orders_2(X1) != iProver_top
% 3.41/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.41/1.00      inference(forward_subsumption_resolution,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_2186,c_629]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9106,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.41/1.00      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 3.41/1.00      | v2_struct_0(X1) = iProver_top
% 3.41/1.00      | v3_orders_2(X1) != iProver_top
% 3.41/1.00      | v4_orders_2(X1) != iProver_top
% 3.41/1.00      | v5_orders_2(X1) != iProver_top
% 3.41/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_632,c_9102]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9118,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.41/1.00      | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
% 3.41/1.00      | v2_struct_0(sK3) = iProver_top
% 3.41/1.00      | v3_orders_2(sK3) != iProver_top
% 3.41/1.00      | v4_orders_2(sK3) != iProver_top
% 3.41/1.00      | v5_orders_2(sK3) != iProver_top
% 3.41/1.00      | l1_orders_2(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_2846,c_9106]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_22,plain,
% 3.41/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_23,plain,
% 3.41/1.00      ( v3_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_24,plain,
% 3.41/1.00      ( v4_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_25,plain,
% 3.41/1.00      ( v5_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_26,plain,
% 3.41/1.00      ( l1_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9297,plain,
% 3.41/1.00      ( r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
% 3.41/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_9118,c_22,c_23,c_24,c_25,c_26]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9298,plain,
% 3.41/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.41/1.00      | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
% 3.41/1.00      inference(renaming,[status(thm)],[c_9297]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/1.00      | ~ r2_hidden(sK0(X1,X0),X0)
% 3.41/1.00      | X0 = X1 ),
% 3.41/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_631,plain,
% 3.41/1.00      ( X0 = X1
% 3.41/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.00      | r2_hidden(sK0(X1,X0),X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9305,plain,
% 3.41/1.00      ( k2_orders_2(sK3,k1_xboole_0) = X0
% 3.41/1.00      | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
% 3.41/1.00      | m1_subset_1(sK0(X0,k2_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_9298,c_631]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9581,plain,
% 3.41/1.00      ( k2_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
% 3.41/1.00      | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_630,c_9305]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_616,plain,
% 3.41/1.00      ( l1_orders_2(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9,plain,
% 3.41/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_623,plain,
% 3.41/1.00      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1082,plain,
% 3.41/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_616,c_623]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_6,plain,
% 3.41/1.00      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.41/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_626,plain,
% 3.41/1.00      ( k1_struct_0(X0) = k1_xboole_0 | l1_struct_0(X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1354,plain,
% 3.41/1.00      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1082,c_626]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_16,negated_conjecture,
% 3.41/1.00      ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1427,plain,
% 3.41/1.00      ( k2_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3) ),
% 3.41/1.00      inference(demodulation,[status(thm)],[c_1354,c_16]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_8,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/1.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/1.00      | v2_struct_0(X1)
% 3.41/1.00      | ~ v3_orders_2(X1)
% 3.41/1.00      | ~ v4_orders_2(X1)
% 3.41/1.00      | ~ v5_orders_2(X1)
% 3.41/1.00      | ~ l1_orders_2(X1) ),
% 3.41/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_922,plain,
% 3.41/1.00      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.41/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.41/1.00      | v2_struct_0(X0)
% 3.41/1.00      | ~ v3_orders_2(X0)
% 3.41/1.00      | ~ v4_orders_2(X0)
% 3.41/1.00      | ~ v5_orders_2(X0)
% 3.41/1.00      | ~ l1_orders_2(X0) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_927,plain,
% 3.41/1.00      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.41/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.41/1.00      | v2_struct_0(X0) = iProver_top
% 3.41/1.00      | v3_orders_2(X0) != iProver_top
% 3.41/1.00      | v4_orders_2(X0) != iProver_top
% 3.41/1.00      | v5_orders_2(X0) != iProver_top
% 3.41/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_929,plain,
% 3.41/1.00      ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.41/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.41/1.00      | v2_struct_0(sK3) = iProver_top
% 3.41/1.00      | v3_orders_2(sK3) != iProver_top
% 3.41/1.00      | v4_orders_2(sK3) != iProver_top
% 3.41/1.00      | v5_orders_2(sK3) != iProver_top
% 3.41/1.00      | l1_orders_2(sK3) != iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_927]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_923,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_925,plain,
% 3.41/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_923]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(contradiction,plain,
% 3.41/1.00      ( $false ),
% 3.41/1.00      inference(minisat,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_9581,c_1427,c_929,c_925,c_26,c_25,c_24,c_23,c_22]) ).
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  ------                               Statistics
% 3.41/1.00  
% 3.41/1.00  ------ Selected
% 3.41/1.00  
% 3.41/1.00  total_time:                             0.308
% 3.41/1.00  
%------------------------------------------------------------------------------
