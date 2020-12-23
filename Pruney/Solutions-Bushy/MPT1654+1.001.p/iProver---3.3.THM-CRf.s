%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1654+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:06 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 929 expanded)
%              Number of clauses        :  104 ( 282 expanded)
%              Number of leaves         :   17 ( 231 expanded)
%              Depth                    :   19
%              Number of atoms          :  528 (4912 expanded)
%              Number of equality atoms :  142 ( 739 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
              & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
            | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
            | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
            | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k1_yellow_0(X0,k5_waybel_0(X0,sK1)) != sK1
          | ~ r1_yellow_0(X0,k5_waybel_0(X0,sK1)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
              | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k1_yellow_0(sK0,k5_waybel_0(sK0,X1)) != X1
            | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,X1)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != sK1
      | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f34,f33])).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_yellow_0(X0,X1)
              | ~ r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
            & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | ~ r1_yellow_0(X0,X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != sK1
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_562,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_794,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_204,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_404,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_13])).

cnf(c_405,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_47,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_50,plain,
    ( l1_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_407,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_17,c_13,c_47,c_50])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0)
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_407])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0) = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),X0_47) = k1_tarski(X0_47) ),
    inference(subtyping,[status(esa)],[c_439])).

cnf(c_802,plain,
    ( k6_domain_1(u1_struct_0(sK0),X0_47) = k1_tarski(X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_1195,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_794,c_802])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_407])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_803,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_1448,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_803])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_607,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_609,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_566,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_955,plain,
    ( X0_47 != X1_47
    | X0_47 = k6_domain_1(u1_struct_0(sK0),X2_47)
    | k6_domain_1(u1_struct_0(sK0),X2_47) != X1_47 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_967,plain,
    ( X0_47 = k6_domain_1(u1_struct_0(sK0),X1_47)
    | X0_47 != k1_tarski(X1_47)
    | k6_domain_1(u1_struct_0(sK0),X1_47) != k1_tarski(X1_47) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1070,plain,
    ( k6_domain_1(u1_struct_0(sK0),X0_47) != k1_tarski(X0_47)
    | k1_tarski(X0_47) = k6_domain_1(u1_struct_0(sK0),X0_47)
    | k1_tarski(X0_47) != k1_tarski(X0_47) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1072,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1)
    | k1_tarski(sK1) != k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_565,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1071,plain,
    ( k1_tarski(X0_47) = k1_tarski(X0_47) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1073,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X0_48)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_894,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X1_47),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_47 != k6_domain_1(u1_struct_0(sK0),X1_47) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tarski(X0_47),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tarski(X0_47) != k6_domain_1(u1_struct_0(sK0),X0_47) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1217,plain,
    ( k1_tarski(X0_47) != k6_domain_1(u1_struct_0(sK0),X0_47)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tarski(X0_47),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_1219,plain,
    ( k1_tarski(sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_1476,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1448,c_12,c_23,c_605,c_609,c_1072,c_1073,c_1219])).

cnf(c_7,plain,
    ( ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k3_waybel_0(X0,X1)) = k1_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_329,plain,
    ( ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k3_waybel_0(X0,X1)) = k1_yellow_0(X0,X1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_330,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,k3_waybel_0(sK0,X0)) = k1_yellow_0(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_16,negated_conjecture,
    ( v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,X0)
    | k1_yellow_0(sK0,k3_waybel_0(sK0,X0)) = k1_yellow_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_17,c_16,c_13])).

cnf(c_335,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_yellow_0(sK0,k3_waybel_0(sK0,X0)) = k1_yellow_0(sK0,X0) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_558,plain,
    ( ~ r1_yellow_0(sK0,X0_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_yellow_0(sK0,k3_waybel_0(sK0,X0_47)) = k1_yellow_0(sK0,X0_47) ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_798,plain,
    ( k1_yellow_0(sK0,k3_waybel_0(sK0,X0_47)) = k1_yellow_0(sK0,X0_47)
    | r1_yellow_0(sK0,X0_47) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1483,plain,
    ( k1_yellow_0(sK0,k3_waybel_0(sK0,k1_tarski(sK1))) = k1_yellow_0(sK0,k1_tarski(sK1))
    | r1_yellow_0(sK0,k1_tarski(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_798])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k5_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = k5_waybel_0(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k5_waybel_0(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k5_waybel_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_17])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) = k5_waybel_0(sK0,X0_47) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_801,plain,
    ( k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) = k5_waybel_0(sK0,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_1044,plain,
    ( k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k5_waybel_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_794,c_801])).

cnf(c_1197,plain,
    ( k3_waybel_0(sK0,k1_tarski(sK1)) = k5_waybel_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1195,c_1044])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_17,c_16,c_13])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_289])).

cnf(c_796,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) = X0_47
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_910,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_794,c_796])).

cnf(c_1199,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1195,c_910])).

cnf(c_1486,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = sK1
    | r1_yellow_0(sK0,k1_tarski(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1483,c_1197,c_1199])).

cnf(c_570,plain,
    ( ~ r1_yellow_0(X0_49,X0_47)
    | r1_yellow_0(X0_49,X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_929,plain,
    ( r1_yellow_0(sK0,X0_47)
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X1_47)))
    | X0_47 != k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X1_47)) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_1361,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)))
    | r1_yellow_0(sK0,k5_waybel_0(sK0,X0_47))
    | k5_waybel_0(sK0,X0_47) != k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1363,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | k5_waybel_0(sK0,sK1) != k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_8,plain,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_266,plain,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_267,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_17,c_16,c_13])).

cnf(c_272,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_561,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_795,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_1206,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK1)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_795])).

cnf(c_1011,plain,
    ( X0_47 != X1_47
    | X0_47 = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X2_47))
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X2_47)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_1093,plain,
    ( X0_47 = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X1_47))
    | X0_47 != k5_waybel_0(sK0,X1_47)
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X1_47)) != k5_waybel_0(sK0,X1_47) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1149,plain,
    ( k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)) != k5_waybel_0(sK0,X0_47)
    | k5_waybel_0(sK0,X0_47) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47))
    | k5_waybel_0(sK0,X0_47) != k5_waybel_0(sK0,X0_47) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1151,plain,
    ( k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k5_waybel_0(sK0,sK1)
    | k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | k5_waybel_0(sK0,sK1) != k5_waybel_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_6,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,k3_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_350,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,k3_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_351,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | r1_yellow_0(sK0,k3_waybel_0(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_yellow_0(sK0,k3_waybel_0(sK0,X0))
    | ~ r1_yellow_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_17,c_16,c_13])).

cnf(c_356,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | r1_yellow_0(sK0,k3_waybel_0(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_355])).

cnf(c_557,plain,
    ( ~ r1_yellow_0(sK0,X0_47)
    | r1_yellow_0(sK0,k3_waybel_0(sK0,X0_47))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_876,plain,
    ( r1_yellow_0(sK0,k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47)))
    | ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0_47))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0_47),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_878,plain,
    ( r1_yellow_0(sK0,k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_608,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_602,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k5_waybel_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_584,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_11,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_563,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_580,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_567,plain,
    ( X0_47 != X1_47
    | k5_waybel_0(X0_49,X0_47) = k5_waybel_0(X0_49,X1_47) ),
    theory(equality)).

cnf(c_573,plain,
    ( k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1486,c_1363,c_1206,c_1151,c_878,c_608,c_602,c_584,c_563,c_580,c_573,c_23,c_12])).


%------------------------------------------------------------------------------
