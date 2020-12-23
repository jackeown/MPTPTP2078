%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:23 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  135 (1822 expanded)
%              Number of clauses        :   76 ( 492 expanded)
%              Number of leaves         :   17 ( 464 expanded)
%              Depth                    :   23
%              Number of atoms          :  465 (9481 expanded)
%              Number of equality atoms :  168 ( 928 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK3,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK3)))
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f36,f35])).

fof(f58,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f61,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_644,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_646,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1132,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_646])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_652,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2043,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1132,c_652])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_645,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2339,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK3,k2_orders_2(sK2,k1_tarski(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_645])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_869,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_872,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_21,c_20])).

cnf(c_641,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_orders_2(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_21,c_20,c_19,c_17])).

cnf(c_643,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_840,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k6_domain_1(u1_struct_0(sK2),X0)) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_643])).

cnf(c_1007,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_840])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1010,plain,
    ( r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_27])).

cnf(c_2338,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | r2_hidden(sK3,k1_tarski(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_1010])).

cnf(c_2474,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2339,c_872,c_2338])).

cnf(c_2485,plain,
    ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_1132])).

cnf(c_2491,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_641])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1909,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_647])).

cnf(c_2987,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_1909])).

cnf(c_4830,plain,
    ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
    | m1_subset_1(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_2987])).

cnf(c_6121,plain,
    ( k6_domain_1(k1_xboole_0,X0) = k1_xboole_0
    | k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
    | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4830,c_652])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_389,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_900,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_787,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | X1 != u1_struct_0(sK2)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1015,plain,
    ( m1_subset_1(sK3,X0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | X0 != u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1017,plain,
    ( X0 != u1_struct_0(sK2)
    | sK3 != sK3
    | m1_subset_1(sK3,X0) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_1019,plain,
    ( sK3 != sK3
    | k1_xboole_0 != u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_390,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1399,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1400,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_21,c_20,c_19,c_17])).

cnf(c_642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_2490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_642])).

cnf(c_2986,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_orders_2(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2490,c_1909])).

cnf(c_4913,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2986])).

cnf(c_4938,plain,
    ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
    | m1_subset_1(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_4913])).

cnf(c_2492,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(k1_xboole_0,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_645])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_653,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2871,plain,
    ( v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_653])).

cnf(c_6174,plain,
    ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
    | m1_subset_1(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4938,c_2871])).

cnf(c_6596,plain,
    ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6121,c_27,c_42,c_43,c_872,c_900,c_1019,c_1400,c_2338,c_6174])).

cnf(c_2486,plain,
    ( r2_hidden(sK3,k6_domain_1(k1_xboole_0,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_1010])).

cnf(c_6606,plain,
    ( r2_hidden(sK3,k1_tarski(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6596,c_2486])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6606,c_872])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:19:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.07/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/1.00  
% 3.07/1.00  ------  iProver source info
% 3.07/1.00  
% 3.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/1.00  git: non_committed_changes: false
% 3.07/1.00  git: last_make_outside_of_git: false
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     num_symb
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       true
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  ------ Parsing...
% 3.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/1.00  ------ Proving...
% 3.07/1.00  ------ Problem Properties 
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  clauses                                 17
% 3.07/1.00  conjectures                             2
% 3.07/1.00  EPR                                     2
% 3.07/1.00  Horn                                    13
% 3.07/1.00  unary                                   5
% 3.07/1.00  binary                                  6
% 3.07/1.00  lits                                    36
% 3.07/1.00  lits eq                                 12
% 3.07/1.00  fd_pure                                 0
% 3.07/1.00  fd_pseudo                               0
% 3.07/1.00  fd_cond                                 2
% 3.07/1.00  fd_pseudo_cond                          2
% 3.07/1.00  AC symbols                              0
% 3.07/1.00  
% 3.07/1.00  ------ Schedule dynamic 5 is on 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  Current options:
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     none
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       false
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ Proving...
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS status Theorem for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  fof(f10,conjecture,(
% 3.07/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f11,negated_conjecture,(
% 3.07/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 3.07/1.00    inference(negated_conjecture,[],[f10])).
% 3.07/1.00  
% 3.07/1.00  fof(f23,plain,(
% 3.07/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f11])).
% 3.07/1.00  
% 3.07/1.00  fof(f24,plain,(
% 3.07/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.07/1.00    inference(flattening,[],[f23])).
% 3.07/1.00  
% 3.07/1.00  fof(f36,plain,(
% 3.07/1.00    ( ! [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK3,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK3))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f35,plain,(
% 3.07/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f37,plain,(
% 3.07/1.00    (r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 3.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f36,f35])).
% 3.07/1.00  
% 3.07/1.00  fof(f58,plain,(
% 3.07/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f7,axiom,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f17,plain,(
% 3.07/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f7])).
% 3.07/1.00  
% 3.07/1.00  fof(f18,plain,(
% 3.07/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.07/1.00    inference(flattening,[],[f17])).
% 3.07/1.00  
% 3.07/1.00  fof(f50,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f18])).
% 3.07/1.00  
% 3.07/1.00  fof(f2,axiom,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f13,plain,(
% 3.07/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f2])).
% 3.07/1.00  
% 3.07/1.00  fof(f40,plain,(
% 3.07/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f13])).
% 3.07/1.00  
% 3.07/1.00  fof(f59,plain,(
% 3.07/1.00    r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f3,axiom,(
% 3.07/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f29,plain,(
% 3.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.07/1.00    inference(nnf_transformation,[],[f3])).
% 3.07/1.00  
% 3.07/1.00  fof(f30,plain,(
% 3.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.07/1.00    inference(rectify,[],[f29])).
% 3.07/1.00  
% 3.07/1.00  fof(f31,plain,(
% 3.07/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f32,plain,(
% 3.07/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.07/1.00  
% 3.07/1.00  fof(f42,plain,(
% 3.07/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.07/1.00    inference(cnf_transformation,[],[f32])).
% 3.07/1.00  
% 3.07/1.00  fof(f60,plain,(
% 3.07/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.07/1.00    inference(equality_resolution,[],[f42])).
% 3.07/1.00  
% 3.07/1.00  fof(f61,plain,(
% 3.07/1.00    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.07/1.00    inference(equality_resolution,[],[f60])).
% 3.07/1.00  
% 3.07/1.00  fof(f8,axiom,(
% 3.07/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f12,plain,(
% 3.07/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.07/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.07/1.00  
% 3.07/1.00  fof(f19,plain,(
% 3.07/1.00    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f12])).
% 3.07/1.00  
% 3.07/1.00  fof(f20,plain,(
% 3.07/1.00    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.07/1.00    inference(flattening,[],[f19])).
% 3.07/1.00  
% 3.07/1.00  fof(f51,plain,(
% 3.07/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f20])).
% 3.07/1.00  
% 3.07/1.00  fof(f57,plain,(
% 3.07/1.00    l1_orders_2(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f53,plain,(
% 3.07/1.00    ~v2_struct_0(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f54,plain,(
% 3.07/1.00    v3_orders_2(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f9,axiom,(
% 3.07/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f21,plain,(
% 3.07/1.00    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f9])).
% 3.07/1.00  
% 3.07/1.00  fof(f22,plain,(
% 3.07/1.00    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.07/1.00    inference(flattening,[],[f21])).
% 3.07/1.00  
% 3.07/1.00  fof(f52,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f22])).
% 3.07/1.00  
% 3.07/1.00  fof(f56,plain,(
% 3.07/1.00    v5_orders_2(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f55,plain,(
% 3.07/1.00    v4_orders_2(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f4,axiom,(
% 3.07/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f33,plain,(
% 3.07/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.07/1.00    inference(nnf_transformation,[],[f4])).
% 3.07/1.00  
% 3.07/1.00  fof(f34,plain,(
% 3.07/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.07/1.00    inference(flattening,[],[f33])).
% 3.07/1.00  
% 3.07/1.00  fof(f47,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.07/1.00    inference(cnf_transformation,[],[f34])).
% 3.07/1.00  
% 3.07/1.00  fof(f63,plain,(
% 3.07/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.07/1.00    inference(equality_resolution,[],[f47])).
% 3.07/1.00  
% 3.07/1.00  fof(f5,axiom,(
% 3.07/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f14,plain,(
% 3.07/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f5])).
% 3.07/1.00  
% 3.07/1.00  fof(f48,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f14])).
% 3.07/1.00  
% 3.07/1.00  fof(f45,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f34])).
% 3.07/1.00  
% 3.07/1.00  fof(f46,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.07/1.00    inference(cnf_transformation,[],[f34])).
% 3.07/1.00  
% 3.07/1.00  fof(f64,plain,(
% 3.07/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.07/1.00    inference(equality_resolution,[],[f46])).
% 3.07/1.00  
% 3.07/1.00  fof(f6,axiom,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f15,plain,(
% 3.07/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f6])).
% 3.07/1.00  
% 3.07/1.00  fof(f16,plain,(
% 3.07/1.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.07/1.00    inference(flattening,[],[f15])).
% 3.07/1.00  
% 3.07/1.00  fof(f49,plain,(
% 3.07/1.00    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f16])).
% 3.07/1.00  
% 3.07/1.00  fof(f1,axiom,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f25,plain,(
% 3.07/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.00    inference(nnf_transformation,[],[f1])).
% 3.07/1.00  
% 3.07/1.00  fof(f26,plain,(
% 3.07/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.00    inference(rectify,[],[f25])).
% 3.07/1.00  
% 3.07/1.00  fof(f27,plain,(
% 3.07/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f28,plain,(
% 3.07/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.07/1.00  
% 3.07/1.00  fof(f38,plain,(
% 3.07/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f28])).
% 3.07/1.00  
% 3.07/1.00  cnf(c_16,negated_conjecture,
% 3.07/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_644,plain,
% 3.07/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_12,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,X1)
% 3.07/1.00      | v1_xboole_0(X1)
% 3.07/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_646,plain,
% 3.07/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.07/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.07/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1132,plain,
% 3.07/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
% 3.07/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_644,c_646]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2,plain,
% 3.07/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_652,plain,
% 3.07/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2043,plain,
% 3.07/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = k1_tarski(sK3)
% 3.07/1.00      | u1_struct_0(sK2) = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1132,c_652]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_15,negated_conjecture,
% 3.07/1.00      ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
% 3.07/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_645,plain,
% 3.07/1.00      ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2339,plain,
% 3.07/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 3.07/1.00      | r2_hidden(sK3,k2_orders_2(sK2,k1_tarski(sK3))) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2043,c_645]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5,plain,
% 3.07/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_869,plain,
% 3.07/1.00      ( r2_hidden(sK3,k1_tarski(sK3)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_872,plain,
% 3.07/1.00      ( r2_hidden(sK3,k1_tarski(sK3)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_13,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.07/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | ~ l1_orders_2(X1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_17,negated_conjecture,
% 3.07/1.00      ( l1_orders_2(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_267,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.07/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | sK2 != X1 ),
% 3.07/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_268,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.07/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | v2_struct_0(sK2)
% 3.07/1.00      | ~ v3_orders_2(sK2) ),
% 3.07/1.00      inference(unflattening,[status(thm)],[c_267]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_21,negated_conjecture,
% 3.07/1.00      ( ~ v2_struct_0(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_20,negated_conjecture,
% 3.07/1.00      ( v3_orders_2(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_272,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.07/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_268,c_21,c_20]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_641,plain,
% 3.07/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_14,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | ~ r2_hidden(X0,X2)
% 3.07/1.00      | ~ r2_hidden(X0,k2_orders_2(X1,X2))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | ~ v4_orders_2(X1)
% 3.07/1.00      | ~ v5_orders_2(X1)
% 3.07/1.00      | ~ l1_orders_2(X1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_18,negated_conjecture,
% 3.07/1.00      ( v5_orders_2(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_217,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | ~ r2_hidden(X0,X2)
% 3.07/1.00      | ~ r2_hidden(X0,k2_orders_2(X1,X2))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | ~ v4_orders_2(X1)
% 3.07/1.00      | ~ l1_orders_2(X1)
% 3.07/1.00      | sK2 != X1 ),
% 3.07/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_218,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.07/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | ~ r2_hidden(X0,X1)
% 3.07/1.00      | ~ r2_hidden(X0,k2_orders_2(sK2,X1))
% 3.07/1.00      | v2_struct_0(sK2)
% 3.07/1.00      | ~ v3_orders_2(sK2)
% 3.07/1.00      | ~ v4_orders_2(sK2)
% 3.07/1.00      | ~ l1_orders_2(sK2) ),
% 3.07/1.00      inference(unflattening,[status(thm)],[c_217]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_19,negated_conjecture,
% 3.07/1.00      ( v4_orders_2(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_222,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.07/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | ~ r2_hidden(X0,X1)
% 3.07/1.00      | ~ r2_hidden(X0,k2_orders_2(sK2,X1)) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_218,c_21,c_20,c_19,c_17]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_643,plain,
% 3.07/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.07/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.07/1.00      | r2_hidden(X0,k2_orders_2(sK2,X1)) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_840,plain,
% 3.07/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | r2_hidden(X1,k6_domain_1(u1_struct_0(sK2),X0)) != iProver_top
% 3.07/1.00      | r2_hidden(X1,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0))) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_641,c_643]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1007,plain,
% 3.07/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_645,c_840]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_27,plain,
% 3.07/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1010,plain,
% 3.07/1.00      ( r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) != iProver_top ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_1007,c_27]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2338,plain,
% 3.07/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 3.07/1.00      | r2_hidden(sK3,k1_tarski(sK3)) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2043,c_1010]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2474,plain,
% 3.07/1.00      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_2339,c_872,c_2338]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2485,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
% 3.07/1.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2474,c_1132]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2491,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.07/1.00      | m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2474,c_641]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_7,plain,
% 3.07/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_10,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_xboole_0(X1)
% 3.07/1.00      | v1_xboole_0(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_647,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1909,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_7,c_647]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2987,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2491,c_1909]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4830,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
% 3.07/1.00      | m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2485,c_2987]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6121,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,X0) = k1_xboole_0
% 3.07/1.00      | k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
% 3.07/1.00      | m1_subset_1(X0,k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_4830,c_652]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_9,plain,
% 3.07/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.07/1.00      | k1_xboole_0 = X0
% 3.07/1.00      | k1_xboole_0 = X1 ),
% 3.07/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_42,plain,
% 3.07/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.07/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_8,plain,
% 3.07/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_43,plain,
% 3.07/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_389,plain,( X0 = X0 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_900,plain,
% 3.07/1.00      ( sK3 = sK3 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_389]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_394,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_787,plain,
% 3.07/1.00      ( m1_subset_1(X0,X1)
% 3.07/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.07/1.00      | X1 != u1_struct_0(sK2)
% 3.07/1.00      | X0 != sK3 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_394]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1015,plain,
% 3.07/1.00      ( m1_subset_1(sK3,X0)
% 3.07/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.07/1.00      | X0 != u1_struct_0(sK2)
% 3.07/1.00      | sK3 != sK3 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1017,plain,
% 3.07/1.00      ( X0 != u1_struct_0(sK2)
% 3.07/1.00      | sK3 != sK3
% 3.07/1.00      | m1_subset_1(sK3,X0) = iProver_top
% 3.07/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1019,plain,
% 3.07/1.00      ( sK3 != sK3
% 3.07/1.00      | k1_xboole_0 != u1_struct_0(sK2)
% 3.07/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.07/1.00      | m1_subset_1(sK3,k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1017]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_390,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1399,plain,
% 3.07/1.00      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_390]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1400,plain,
% 3.07/1.00      ( u1_struct_0(sK2) != k1_xboole_0
% 3.07/1.00      | k1_xboole_0 = u1_struct_0(sK2)
% 3.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_11,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | ~ v4_orders_2(X1)
% 3.07/1.00      | ~ v5_orders_2(X1)
% 3.07/1.00      | ~ l1_orders_2(X1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_241,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/1.00      | v2_struct_0(X1)
% 3.07/1.00      | ~ v3_orders_2(X1)
% 3.07/1.00      | ~ v4_orders_2(X1)
% 3.07/1.00      | ~ l1_orders_2(X1)
% 3.07/1.00      | sK2 != X1 ),
% 3.07/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_242,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | v2_struct_0(sK2)
% 3.07/1.00      | ~ v3_orders_2(sK2)
% 3.07/1.00      | ~ v4_orders_2(sK2)
% 3.07/1.00      | ~ l1_orders_2(sK2) ),
% 3.07/1.00      inference(unflattening,[status(thm)],[c_241]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_246,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.07/1.00      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_242,c_21,c_20,c_19,c_17]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_642,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2490,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2474,c_642]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2986,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(k2_orders_2(sK2,X0)) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2490,c_1909]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4913,plain,
% 3.07/1.00      ( m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,X0))) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2491,c_2986]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4938,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
% 3.07/1.00      | m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,X0))) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2485,c_4913]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2492,plain,
% 3.07/1.00      ( r2_hidden(sK3,k2_orders_2(sK2,k6_domain_1(k1_xboole_0,sK3))) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2474,c_645]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1,plain,
% 3.07/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_653,plain,
% 3.07/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.07/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2871,plain,
% 3.07/1.00      ( v1_xboole_0(k2_orders_2(sK2,k6_domain_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2492,c_653]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6174,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3)
% 3.07/1.00      | m1_subset_1(sK3,k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_4938,c_2871]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6596,plain,
% 3.07/1.00      ( k6_domain_1(k1_xboole_0,sK3) = k1_tarski(sK3) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_6121,c_27,c_42,c_43,c_872,c_900,c_1019,c_1400,c_2338,
% 3.07/1.00                 c_6174]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2486,plain,
% 3.07/1.00      ( r2_hidden(sK3,k6_domain_1(k1_xboole_0,sK3)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2474,c_1010]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6606,plain,
% 3.07/1.00      ( r2_hidden(sK3,k1_tarski(sK3)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_6596,c_2486]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(contradiction,plain,
% 3.07/1.00      ( $false ),
% 3.07/1.00      inference(minisat,[status(thm)],[c_6606,c_872]) ).
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  ------                               Statistics
% 3.07/1.00  
% 3.07/1.00  ------ General
% 3.07/1.00  
% 3.07/1.00  abstr_ref_over_cycles:                  0
% 3.07/1.00  abstr_ref_under_cycles:                 0
% 3.07/1.00  gc_basic_clause_elim:                   0
% 3.07/1.00  forced_gc_time:                         0
% 3.07/1.00  parsing_time:                           0.013
% 3.07/1.00  unif_index_cands_time:                  0.
% 3.07/1.00  unif_index_add_time:                    0.
% 3.07/1.00  orderings_time:                         0.
% 3.07/1.00  out_proof_time:                         0.016
% 3.07/1.00  total_time:                             0.293
% 3.07/1.00  num_of_symbols:                         50
% 3.07/1.00  num_of_terms:                           6310
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing
% 3.07/1.00  
% 3.07/1.00  num_of_splits:                          0
% 3.07/1.00  num_of_split_atoms:                     0
% 3.07/1.00  num_of_reused_defs:                     0
% 3.07/1.00  num_eq_ax_congr_red:                    15
% 3.07/1.00  num_of_sem_filtered_clauses:            1
% 3.07/1.00  num_of_subtypes:                        0
% 3.07/1.00  monotx_restored_types:                  0
% 3.07/1.00  sat_num_of_epr_types:                   0
% 3.07/1.00  sat_num_of_non_cyclic_types:            0
% 3.07/1.00  sat_guarded_non_collapsed_types:        0
% 3.07/1.00  num_pure_diseq_elim:                    0
% 3.07/1.00  simp_replaced_by:                       0
% 3.07/1.00  res_preprocessed:                       92
% 3.07/1.00  prep_upred:                             0
% 3.07/1.00  prep_unflattend:                        3
% 3.07/1.00  smt_new_axioms:                         0
% 3.07/1.00  pred_elim_cands:                        3
% 3.07/1.00  pred_elim:                              5
% 3.07/1.00  pred_elim_cl:                           5
% 3.07/1.00  pred_elim_cycles:                       7
% 3.07/1.00  merged_defs:                            0
% 3.07/1.00  merged_defs_ncl:                        0
% 3.07/1.00  bin_hyper_res:                          0
% 3.07/1.00  prep_cycles:                            4
% 3.07/1.00  pred_elim_time:                         0.002
% 3.07/1.00  splitting_time:                         0.
% 3.07/1.00  sem_filter_time:                        0.
% 3.07/1.00  monotx_time:                            0.
% 3.07/1.00  subtype_inf_time:                       0.
% 3.07/1.00  
% 3.07/1.00  ------ Problem properties
% 3.07/1.00  
% 3.07/1.00  clauses:                                17
% 3.07/1.00  conjectures:                            2
% 3.07/1.00  epr:                                    2
% 3.07/1.00  horn:                                   13
% 3.07/1.00  ground:                                 2
% 3.07/1.00  unary:                                  5
% 3.07/1.00  binary:                                 6
% 3.07/1.00  lits:                                   36
% 3.07/1.00  lits_eq:                                12
% 3.07/1.00  fd_pure:                                0
% 3.07/1.00  fd_pseudo:                              0
% 3.07/1.00  fd_cond:                                2
% 3.07/1.00  fd_pseudo_cond:                         2
% 3.07/1.00  ac_symbols:                             0
% 3.07/1.00  
% 3.07/1.00  ------ Propositional Solver
% 3.07/1.00  
% 3.07/1.00  prop_solver_calls:                      27
% 3.07/1.00  prop_fast_solver_calls:                 676
% 3.07/1.00  smt_solver_calls:                       0
% 3.07/1.00  smt_fast_solver_calls:                  0
% 3.07/1.00  prop_num_of_clauses:                    2668
% 3.07/1.00  prop_preprocess_simplified:             6603
% 3.07/1.00  prop_fo_subsumed:                       17
% 3.07/1.00  prop_solver_time:                       0.
% 3.07/1.00  smt_solver_time:                        0.
% 3.07/1.00  smt_fast_solver_time:                   0.
% 3.07/1.00  prop_fast_solver_time:                  0.
% 3.07/1.00  prop_unsat_core_time:                   0.
% 3.07/1.00  
% 3.07/1.00  ------ QBF
% 3.07/1.00  
% 3.07/1.00  qbf_q_res:                              0
% 3.07/1.00  qbf_num_tautologies:                    0
% 3.07/1.00  qbf_prep_cycles:                        0
% 3.07/1.00  
% 3.07/1.00  ------ BMC1
% 3.07/1.00  
% 3.07/1.00  bmc1_current_bound:                     -1
% 3.07/1.00  bmc1_last_solved_bound:                 -1
% 3.07/1.00  bmc1_unsat_core_size:                   -1
% 3.07/1.00  bmc1_unsat_core_parents_size:           -1
% 3.07/1.00  bmc1_merge_next_fun:                    0
% 3.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation
% 3.07/1.00  
% 3.07/1.00  inst_num_of_clauses:                    883
% 3.07/1.00  inst_num_in_passive:                    233
% 3.07/1.00  inst_num_in_active:                     320
% 3.07/1.00  inst_num_in_unprocessed:                330
% 3.07/1.00  inst_num_of_loops:                      380
% 3.07/1.00  inst_num_of_learning_restarts:          0
% 3.07/1.00  inst_num_moves_active_passive:          59
% 3.07/1.00  inst_lit_activity:                      0
% 3.07/1.00  inst_lit_activity_moves:                0
% 3.07/1.00  inst_num_tautologies:                   0
% 3.07/1.00  inst_num_prop_implied:                  0
% 3.07/1.00  inst_num_existing_simplified:           0
% 3.07/1.00  inst_num_eq_res_simplified:             0
% 3.07/1.00  inst_num_child_elim:                    0
% 3.07/1.00  inst_num_of_dismatching_blockings:      247
% 3.07/1.00  inst_num_of_non_proper_insts:           694
% 3.07/1.00  inst_num_of_duplicates:                 0
% 3.07/1.00  inst_inst_num_from_inst_to_res:         0
% 3.07/1.00  inst_dismatching_checking_time:         0.
% 3.07/1.00  
% 3.07/1.00  ------ Resolution
% 3.07/1.00  
% 3.07/1.00  res_num_of_clauses:                     0
% 3.07/1.00  res_num_in_passive:                     0
% 3.07/1.00  res_num_in_active:                      0
% 3.07/1.00  res_num_of_loops:                       96
% 3.07/1.00  res_forward_subset_subsumed:            48
% 3.07/1.00  res_backward_subset_subsumed:           0
% 3.07/1.00  res_forward_subsumed:                   0
% 3.07/1.00  res_backward_subsumed:                  0
% 3.07/1.00  res_forward_subsumption_resolution:     0
% 3.07/1.00  res_backward_subsumption_resolution:    0
% 3.07/1.00  res_clause_to_clause_subsumption:       272
% 3.07/1.00  res_orphan_elimination:                 0
% 3.07/1.00  res_tautology_del:                      34
% 3.07/1.00  res_num_eq_res_simplified:              0
% 3.07/1.00  res_num_sel_changes:                    0
% 3.07/1.00  res_moves_from_active_to_pass:          0
% 3.07/1.00  
% 3.07/1.00  ------ Superposition
% 3.07/1.00  
% 3.07/1.00  sup_time_total:                         0.
% 3.07/1.00  sup_time_generating:                    0.
% 3.07/1.00  sup_time_sim_full:                      0.
% 3.07/1.00  sup_time_sim_immed:                     0.
% 3.07/1.00  
% 3.07/1.00  sup_num_of_clauses:                     86
% 3.07/1.00  sup_num_in_active:                      44
% 3.07/1.00  sup_num_in_passive:                     42
% 3.07/1.00  sup_num_of_loops:                       74
% 3.07/1.00  sup_fw_superposition:                   72
% 3.07/1.00  sup_bw_superposition:                   54
% 3.07/1.00  sup_immediate_simplified:               18
% 3.07/1.00  sup_given_eliminated:                   0
% 3.07/1.00  comparisons_done:                       0
% 3.07/1.00  comparisons_avoided:                    28
% 3.07/1.00  
% 3.07/1.00  ------ Simplifications
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  sim_fw_subset_subsumed:                 10
% 3.07/1.00  sim_bw_subset_subsumed:                 21
% 3.07/1.00  sim_fw_subsumed:                        6
% 3.07/1.00  sim_bw_subsumed:                        2
% 3.07/1.00  sim_fw_subsumption_res:                 1
% 3.07/1.00  sim_bw_subsumption_res:                 0
% 3.07/1.00  sim_tautology_del:                      1
% 3.07/1.00  sim_eq_tautology_del:                   5
% 3.07/1.00  sim_eq_res_simp:                        0
% 3.07/1.00  sim_fw_demodulated:                     0
% 3.07/1.00  sim_bw_demodulated:                     26
% 3.07/1.00  sim_light_normalised:                   7
% 3.07/1.00  sim_joinable_taut:                      0
% 3.07/1.00  sim_joinable_simp:                      0
% 3.07/1.00  sim_ac_normalised:                      0
% 3.07/1.00  sim_smt_subsumption:                    0
% 3.07/1.00  
%------------------------------------------------------------------------------
