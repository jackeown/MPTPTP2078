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
% DateTime   : Thu Dec  3 12:18:59 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  226 (2026 expanded)
%              Number of clauses        :  131 ( 422 expanded)
%              Number of leaves         :   20 ( 532 expanded)
%              Depth                    :   27
%              Number of atoms          : 1120 (13939 expanded)
%              Number of equality atoms :  249 ( 658 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | ~ r3_lattices(X0,X1,X2) )
              & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | ~ r3_lattices(X0,X1,X2) )
              & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
            | ~ r3_lattices(X0,X1,X2) )
          & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
            | r3_lattices(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,sK3))
          | ~ r3_lattices(X0,X1,sK3) )
        & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,sK3))
          | r3_lattices(X0,X1,sK3) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | ~ r3_lattices(X0,X1,X2) )
              & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK2),k4_lattice3(X0,X2))
              | ~ r3_lattices(X0,sK2,X2) )
            & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK2),k4_lattice3(X0,X2))
              | r3_lattices(X0,sK2,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | r3_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,X1),k4_lattice3(sK1,X2))
                | ~ r3_lattices(sK1,X1,X2) )
              & ( r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,X1),k4_lattice3(sK1,X2))
                | r3_lattices(sK1,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
      | ~ r3_lattices(sK1,sK2,sK3) )
    & ( r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
      | r3_lattices(sK1,sK2,sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f66,f65,f64])).

fof(f93,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f84,plain,(
    ! [X0] :
      ( v1_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    ! [X0] :
      ( l1_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f94,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = k2_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f91,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                  | ~ r3_lattices(X0,X1,X2) )
                & ( r3_lattices(X0,X1,X2)
                  | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,
    ( r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
    | r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ! [X0] :
      ( v3_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ( v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( ( v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f96,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f59])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,
    ( ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
    | ~ r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1668,plain,
    ( v10_lattices(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v1_orders_2(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_396,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = X1
    | k3_lattice3(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_397,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(k3_lattice3(X0))
    | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_16,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | l1_orders_2(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_401,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_16])).

cnf(c_402,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_1666,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0)
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_3344,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1)
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1666])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_56,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | l1_orders_2(k3_lattice3(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_399,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(k3_lattice3(sK1))
    | g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_3522,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3344,c_30,c_29,c_28,c_56,c_399])).

cnf(c_13,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1677,plain,
    ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2542,plain,
    ( g1_orders_2(u1_struct_0(sK1),k2_lattice3(sK1)) = k3_lattice3(sK1)
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1677])).

cnf(c_23,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattice3(X0) = k8_filter_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1672,plain,
    ( k2_lattice3(X0) = k8_filter_1(X0)
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2128,plain,
    ( k2_lattice3(sK1) = k8_filter_1(sK1)
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1672])).

cnf(c_39,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattice3(sK1) = k8_filter_1(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2286,plain,
    ( k2_lattice3(sK1) = k8_filter_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_30,c_29,c_28,c_39])).

cnf(c_2543,plain,
    ( g1_orders_2(u1_struct_0(sK1),k8_filter_1(sK1)) = k3_lattice3(sK1)
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2542,c_2286])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( l3_lattices(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4217,plain,
    ( g1_orders_2(u1_struct_0(sK1),k8_filter_1(sK1)) = k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2543,c_31,c_33])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1682,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4222,plain,
    ( g1_orders_2(X0,X1) != k3_lattice3(sK1)
    | k8_filter_1(sK1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4217,c_1682])).

cnf(c_32,plain,
    ( v10_lattices(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1675,plain,
    ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2600,plain,
    ( m1_subset_1(k8_filter_1(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2286,c_1675])).

cnf(c_4223,plain,
    ( g1_orders_2(X0,X1) != k3_lattice3(sK1)
    | k8_filter_1(sK1) = X1
    | m1_subset_1(k8_filter_1(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4217,c_1682])).

cnf(c_4868,plain,
    ( k8_filter_1(sK1) = X1
    | g1_orders_2(X0,X1) != k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4222,c_31,c_32,c_33,c_2600,c_4223])).

cnf(c_4869,plain,
    ( g1_orders_2(X0,X1) != k3_lattice3(sK1)
    | k8_filter_1(sK1) = X1 ),
    inference(renaming,[status(thm)],[c_4868])).

cnf(c_4873,plain,
    ( u1_orders_2(k3_lattice3(sK1)) = k8_filter_1(sK1) ),
    inference(superposition,[status(thm)],[c_3522,c_4869])).

cnf(c_11,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( r3_lattices(sK1,sK2,sK3)
    | r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_228,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v3_orders_2(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_425,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_426,plain,
    ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
    | r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k3_lattice3(X0))
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_22,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k3_lattice3(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_430,plain,
    ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
    | r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_22,c_16])).

cnf(c_577,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k4_lattice3(sK1,sK3) != X2
    | k4_lattice3(sK1,sK2) != X1
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_228,c_430])).

cnf(c_578,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r1_orders_2(k3_lattice3(X0),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_777,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X2)
    | k4_lattice3(sK1,sK3) != X1
    | k4_lattice3(sK1,sK2) != X0
    | k3_lattice3(X3) != X2
    | k3_lattice3(X3) != k3_lattice3(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_578])).

cnf(c_778,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(k3_lattice3(X0))
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_782,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | r3_lattices(sK1,sK2,sK3)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_778,c_16])).

cnf(c_783,plain,
    ( r3_lattices(sK1,sK2,sK3)
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(renaming,[status(thm)],[c_782])).

cnf(c_1015,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | k3_lattice3(X3) != k3_lattice3(sK1)
    | sK3 != X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_783])).

cnf(c_1016,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_lattices(X0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1020,plain,
    ( v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | ~ l3_lattices(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_30,c_29,c_28,c_27,c_26])).

cnf(c_1021,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(renaming,[status(thm)],[c_1020])).

cnf(c_1661,plain,
    ( k3_lattice3(X0) != k3_lattice3(sK1)
    | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0))) = iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0))) != iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1999,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1661])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1932,plain,
    ( m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1933,plain,
    ( m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_1935,plain,
    ( m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1936,plain,
    ( m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_3888,plain,
    ( r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1999,c_31,c_32,c_33,c_34,c_35,c_1933,c_1936])).

cnf(c_3889,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3888])).

cnf(c_1671,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1676,plain,
    ( k4_lattice3(X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2751,plain,
    ( k4_lattice3(sK1,sK3) = sK3
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1676])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k4_lattice3(sK1,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2856,plain,
    ( k4_lattice3(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2751,c_30,c_29,c_28,c_26,c_1926])).

cnf(c_1670,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2752,plain,
    ( k4_lattice3(sK1,sK2) = sK2
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_1676])).

cnf(c_1929,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | k4_lattice3(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2948,plain,
    ( k4_lattice3(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2752,c_30,c_29,c_28,c_27,c_1929])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | k1_domain_1(X3,X1,X2,X0) = k4_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1680,plain,
    ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2779,plain,
    ( k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1680])).

cnf(c_10,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_73,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_75,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_9,plain,
    ( ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_76,plain,
    ( v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_78,plain,
    ( v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(sK0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2556,plain,
    ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(sK0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_2558,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(sK0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_3004,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2779,c_31,c_32,c_33,c_75,c_78,c_2558])).

cnf(c_3005,plain,
    ( k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3004])).

cnf(c_3016,plain,
    ( k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_3005])).

cnf(c_74,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_77,plain,
    ( ~ v10_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1974,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_domain_1(X1,u1_struct_0(sK1),X0,sK3) = k4_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2092,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_3154,plain,
    ( k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3016,c_30,c_29,c_28,c_27,c_26,c_74,c_77,c_2092,c_2556])).

cnf(c_3892,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) = iProver_top
    | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(k3_lattice3(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3889,c_2856,c_2948,c_3154])).

cnf(c_5076,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4873,c_3892])).

cnf(c_12,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_226,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_458,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X0)
    | k3_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_459,plain,
    ( r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k3_lattice3(X0))
    | ~ l1_orders_2(k3_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_463,plain,
    ( r3_orders_2(k3_lattice3(X0),X1,X2)
    | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_22,c_16])).

cnf(c_607,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k4_lattice3(sK1,sK3) != X2
    | k4_lattice3(sK1,sK2) != X1
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_226,c_463])).

cnf(c_608,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r1_orders_2(k3_lattice3(X0),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_741,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | ~ l1_orders_2(X2)
    | k4_lattice3(sK1,sK3) != X1
    | k4_lattice3(sK1,sK2) != X0
    | k3_lattice3(X3) != X2
    | k3_lattice3(X3) != k3_lattice3(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_608])).

cnf(c_742,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(k3_lattice3(X0))
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_746,plain,
    ( v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ v10_lattices(X0)
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ r3_lattices(sK1,sK2,sK3)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_16])).

cnf(c_747,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(renaming,[status(thm)],[c_746])).

cnf(c_979,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | k3_lattice3(X3) != k3_lattice3(sK1)
    | sK3 != X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_747])).

cnf(c_980,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_lattices(X0)
    | ~ v10_lattices(sK1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_984,plain,
    ( v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | ~ l3_lattices(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_980,c_30,c_29,c_28,c_27,c_26])).

cnf(c_985,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
    | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
    | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k3_lattice3(X0) != k3_lattice3(sK1) ),
    inference(renaming,[status(thm)],[c_984])).

cnf(c_1662,plain,
    ( k3_lattice3(X0) != k3_lattice3(sK1)
    | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0))) != iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_2436,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) != iProver_top
    | v10_lattices(sK1) != iProver_top
    | l3_lattices(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1662])).

cnf(c_2512,plain,
    ( r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_31,c_32,c_33,c_34,c_35,c_1933,c_1936])).

cnf(c_2513,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2512])).

cnf(c_2860,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
    | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),sK3),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2856,c_2513])).

cnf(c_3801,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) != iProver_top
    | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2860,c_2948,c_3154])).

cnf(c_5077,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4873,c_3801])).

cnf(c_5087,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5076,c_5077])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:30:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.99  
% 3.00/0.99  ------  iProver source info
% 3.00/0.99  
% 3.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.99  git: non_committed_changes: false
% 3.00/0.99  git: last_make_outside_of_git: false
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     num_symb
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       true
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  ------ Parsing...
% 3.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.99  ------ Proving...
% 3.00/0.99  ------ Problem Properties 
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  clauses                                 23
% 3.00/0.99  conjectures                             5
% 3.00/0.99  EPR                                     4
% 3.00/0.99  Horn                                    12
% 3.00/0.99  unary                                   5
% 3.00/0.99  binary                                  1
% 3.00/0.99  lits                                    91
% 3.00/0.99  lits eq                                 13
% 3.00/0.99  fd_pure                                 0
% 3.00/0.99  fd_pseudo                               0
% 3.00/0.99  fd_cond                                 0
% 3.00/0.99  fd_pseudo_cond                          2
% 3.00/0.99  AC symbols                              0
% 3.00/0.99  
% 3.00/0.99  ------ Schedule dynamic 5 is on 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  Current options:
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     none
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       false
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ Proving...
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS status Theorem for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99   Resolution empty clause
% 3.00/0.99  
% 3.00/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  fof(f16,conjecture,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f17,negated_conjecture,(
% 3.00/0.99    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 3.00/0.99    inference(negated_conjecture,[],[f16])).
% 3.00/0.99  
% 3.00/0.99  fof(f55,plain,(
% 3.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_lattices(X0,X1,X2) <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f17])).
% 3.00/0.99  
% 3.00/0.99  fof(f56,plain,(
% 3.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_lattices(X0,X1,X2) <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f55])).
% 3.00/0.99  
% 3.00/0.99  fof(f62,plain,(
% 3.00/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.00/0.99    inference(nnf_transformation,[],[f56])).
% 3.00/0.99  
% 3.00/0.99  fof(f63,plain,(
% 3.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f62])).
% 3.00/0.99  
% 3.00/0.99  fof(f66,plain,(
% 3.00/0.99    ( ! [X0,X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,sK3)) | ~r3_lattices(X0,X1,sK3)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,sK3)) | r3_lattices(X0,X1,sK3)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f65,plain,(
% 3.00/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK2),k4_lattice3(X0,X2)) | ~r3_lattices(X0,sK2,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,sK2),k4_lattice3(X0,X2)) | r3_lattices(X0,sK2,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f64,plain,(
% 3.00/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,X1),k4_lattice3(sK1,X2)) | ~r3_lattices(sK1,X1,X2)) & (r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,X1),k4_lattice3(sK1,X2)) | r3_lattices(sK1,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f67,plain,(
% 3.00/0.99    (((~r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) | ~r3_lattices(sK1,sK2,sK3)) & (r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) | r3_lattices(sK1,sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f63,f66,f65,f64])).
% 3.00/0.99  
% 3.00/0.99  fof(f93,plain,(
% 3.00/0.99    v10_lattices(sK1)),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f2,axiom,(
% 3.00/0.99    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f29,plain,(
% 3.00/0.99    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 3.00/0.99    inference(ennf_transformation,[],[f2])).
% 3.00/0.99  
% 3.00/0.99  fof(f30,plain,(
% 3.00/0.99    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 3.00/0.99    inference(flattening,[],[f29])).
% 3.00/0.99  
% 3.00/0.99  fof(f69,plain,(
% 3.00/0.99    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f30])).
% 3.00/0.99  
% 3.00/0.99  fof(f12,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f19,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.00/0.99  
% 3.00/0.99  fof(f20,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.00/0.99  
% 3.00/0.99  fof(f47,plain,(
% 3.00/0.99    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f20])).
% 3.00/0.99  
% 3.00/0.99  fof(f48,plain,(
% 3.00/0.99    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f47])).
% 3.00/0.99  
% 3.00/0.99  fof(f84,plain,(
% 3.00/0.99    ( ! [X0] : (v1_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f48])).
% 3.00/0.99  
% 3.00/0.99  fof(f86,plain,(
% 3.00/0.99    ( ! [X0] : (l1_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f48])).
% 3.00/0.99  
% 3.00/0.99  fof(f92,plain,(
% 3.00/0.99    ~v2_struct_0(sK1)),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f94,plain,(
% 3.00/0.99    l3_lattices(sK1)),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f9,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f41,plain,(
% 3.00/0.99    ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f9])).
% 3.00/0.99  
% 3.00/0.99  fof(f42,plain,(
% 3.00/0.99    ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f41])).
% 3.00/0.99  
% 3.00/0.99  fof(f81,plain,(
% 3.00/0.99    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f42])).
% 3.00/0.99  
% 3.00/0.99  fof(f15,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k8_filter_1(X0) = k2_lattice3(X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f53,plain,(
% 3.00/0.99    ! [X0] : (k8_filter_1(X0) = k2_lattice3(X0) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f54,plain,(
% 3.00/0.99    ! [X0] : (k8_filter_1(X0) = k2_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f53])).
% 3.00/0.99  
% 3.00/0.99  fof(f91,plain,(
% 3.00/0.99    ( ! [X0] : (k8_filter_1(X0) = k2_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f54])).
% 3.00/0.99  
% 3.00/0.99  fof(f4,axiom,(
% 3.00/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f32,plain,(
% 3.00/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.00/0.99    inference(ennf_transformation,[],[f4])).
% 3.00/0.99  
% 3.00/0.99  fof(f73,plain,(
% 3.00/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f32])).
% 3.00/0.99  
% 3.00/0.99  fof(f11,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f22,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.00/0.99  
% 3.00/0.99  fof(f23,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f22])).
% 3.00/0.99  
% 3.00/0.99  fof(f24,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f23])).
% 3.00/0.99  
% 3.00/0.99  fof(f25,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f24])).
% 3.00/0.99  
% 3.00/0.99  fof(f45,plain,(
% 3.00/0.99    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f25])).
% 3.00/0.99  
% 3.00/0.99  fof(f46,plain,(
% 3.00/0.99    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f45])).
% 3.00/0.99  
% 3.00/0.99  fof(f83,plain,(
% 3.00/0.99    ( ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f46])).
% 3.00/0.99  
% 3.00/0.99  fof(f8,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f39,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f8])).
% 3.00/0.99  
% 3.00/0.99  fof(f40,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f39])).
% 3.00/0.99  
% 3.00/0.99  fof(f61,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~r3_lattices(X0,X1,X2)) & (r3_lattices(X0,X1,X2) | ~r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(nnf_transformation,[],[f40])).
% 3.00/0.99  
% 3.00/0.99  fof(f80,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f61])).
% 3.00/0.99  
% 3.00/0.99  fof(f3,axiom,(
% 3.00/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f31,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.00/0.99    inference(ennf_transformation,[],[f3])).
% 3.00/0.99  
% 3.00/0.99  fof(f57,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.00/0.99    inference(nnf_transformation,[],[f31])).
% 3.00/0.99  
% 3.00/0.99  fof(f70,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f57])).
% 3.00/0.99  
% 3.00/0.99  fof(f97,plain,(
% 3.00/0.99    r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) | r3_lattices(sK1,sK2,sK3)),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f6,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f35,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f6])).
% 3.00/0.99  
% 3.00/0.99  fof(f36,plain,(
% 3.00/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f35])).
% 3.00/0.99  
% 3.00/0.99  fof(f58,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(nnf_transformation,[],[f36])).
% 3.00/0.99  
% 3.00/0.99  fof(f75,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f58])).
% 3.00/0.99  
% 3.00/0.99  fof(f85,plain,(
% 3.00/0.99    ( ! [X0] : (v3_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f48])).
% 3.00/0.99  
% 3.00/0.99  fof(f14,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f18,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.00/0.99  
% 3.00/0.99  fof(f21,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.00/0.99  
% 3.00/0.99  fof(f51,plain,(
% 3.00/0.99    ! [X0] : ((v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f21])).
% 3.00/0.99  
% 3.00/0.99  fof(f52,plain,(
% 3.00/0.99    ! [X0] : ((v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f51])).
% 3.00/0.99  
% 3.00/0.99  fof(f88,plain,(
% 3.00/0.99    ( ! [X0] : (~v2_struct_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f52])).
% 3.00/0.99  
% 3.00/0.99  fof(f95,plain,(
% 3.00/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f96,plain,(
% 3.00/0.99    m1_subset_1(sK3,u1_struct_0(sK1))),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f13,axiom,(
% 3.00/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f49,plain,(
% 3.00/0.99    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f13])).
% 3.00/0.99  
% 3.00/0.99  fof(f50,plain,(
% 3.00/0.99    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f49])).
% 3.00/0.99  
% 3.00/0.99  fof(f87,plain,(
% 3.00/0.99    ( ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f50])).
% 3.00/0.99  
% 3.00/0.99  fof(f10,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f43,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f10])).
% 3.00/0.99  
% 3.00/0.99  fof(f44,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f43])).
% 3.00/0.99  
% 3.00/0.99  fof(f82,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f44])).
% 3.00/0.99  
% 3.00/0.99  fof(f5,axiom,(
% 3.00/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X1) & m1_subset_1(X2,X0) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f33,plain,(
% 3.00/0.99    ! [X0,X1,X2,X3] : (k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) | (~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f5])).
% 3.00/0.99  
% 3.00/0.99  fof(f34,plain,(
% 3.00/0.99    ! [X0,X1,X2,X3] : (k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.00/0.99    inference(flattening,[],[f33])).
% 3.00/0.99  
% 3.00/0.99  fof(f74,plain,(
% 3.00/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f34])).
% 3.00/0.99  
% 3.00/0.99  fof(f7,axiom,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ? [X1] : (v19_lattices(X1,X0) & v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f26,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ? [X1] : (v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.00/0.99  
% 3.00/0.99  fof(f27,plain,(
% 3.00/0.99    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f26])).
% 3.00/0.99  
% 3.00/0.99  fof(f37,plain,(
% 3.00/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f27])).
% 3.00/0.99  
% 3.00/0.99  fof(f38,plain,(
% 3.00/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(flattening,[],[f37])).
% 3.00/0.99  
% 3.00/0.99  fof(f59,plain,(
% 3.00/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f60,plain,(
% 3.00/0.99    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f59])).
% 3.00/0.99  
% 3.00/0.99  fof(f77,plain,(
% 3.00/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f60])).
% 3.00/0.99  
% 3.00/0.99  fof(f78,plain,(
% 3.00/0.99    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f60])).
% 3.00/0.99  
% 3.00/0.99  fof(f1,axiom,(
% 3.00/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f28,plain,(
% 3.00/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.00/0.99    inference(ennf_transformation,[],[f1])).
% 3.00/0.99  
% 3.00/0.99  fof(f68,plain,(
% 3.00/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f79,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f61])).
% 3.00/0.99  
% 3.00/0.99  fof(f71,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f57])).
% 3.00/0.99  
% 3.00/0.99  fof(f98,plain,(
% 3.00/0.99    ~r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) | ~r3_lattices(sK1,sK2,sK3)),
% 3.00/0.99    inference(cnf_transformation,[],[f67])).
% 3.00/0.99  
% 3.00/0.99  fof(f76,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f58])).
% 3.00/0.99  
% 3.00/0.99  cnf(c_29,negated_conjecture,
% 3.00/0.99      ( v10_lattices(sK1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1668,plain,
% 3.00/0.99      ( v10_lattices(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1,plain,
% 3.00/0.99      ( ~ l1_orders_2(X0)
% 3.00/0.99      | ~ v1_orders_2(X0)
% 3.00/0.99      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_18,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v1_orders_2(k3_lattice3(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_396,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ l1_orders_2(X1)
% 3.00/0.99      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = X1
% 3.00/0.99      | k3_lattice3(X0) != X1 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_397,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(X0))
% 3.00/0.99      | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_16,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | l1_orders_2(k3_lattice3(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_401,plain,
% 3.00/0.99      ( v2_struct_0(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
% 3.00/0.99      inference(global_propositional_subsumption,[status(thm)],[c_397,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_402,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0) ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_401]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1666,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(k3_lattice3(X0)),u1_orders_2(k3_lattice3(X0))) = k3_lattice3(X0)
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3344,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1)
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1668,c_1666]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_30,negated_conjecture,
% 3.00/0.99      ( ~ v2_struct_0(sK1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_28,negated_conjecture,
% 3.00/0.99      ( l3_lattices(sK1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_56,plain,
% 3.00/0.99      ( ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | l1_orders_2(k3_lattice3(sK1)) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_399,plain,
% 3.00/0.99      ( ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(sK1))
% 3.00/0.99      | g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_397]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3522,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(k3_lattice3(sK1)),u1_orders_2(k3_lattice3(sK1))) = k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_3344,c_30,c_29,c_28,c_56,c_399]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_13,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1677,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2542,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(sK1),k2_lattice3(sK1)) = k3_lattice3(sK1)
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1668,c_1677]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_23,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k2_lattice3(X0) = k8_filter_1(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1672,plain,
% 3.00/0.99      ( k2_lattice3(X0) = k8_filter_1(X0)
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2128,plain,
% 3.00/0.99      ( k2_lattice3(sK1) = k8_filter_1(sK1)
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1668,c_1672]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_39,plain,
% 3.00/0.99      ( ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | k2_lattice3(sK1) = k8_filter_1(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2286,plain,
% 3.00/0.99      ( k2_lattice3(sK1) = k8_filter_1(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_2128,c_30,c_29,c_28,c_39]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2543,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(sK1),k8_filter_1(sK1)) = k3_lattice3(sK1)
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2542,c_2286]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_31,plain,
% 3.00/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_33,plain,
% 3.00/0.99      ( l3_lattices(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4217,plain,
% 3.00/0.99      ( g1_orders_2(u1_struct_0(sK1),k8_filter_1(sK1)) = k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_2543,c_31,c_33]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.00/0.99      | X2 = X0
% 3.00/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1682,plain,
% 3.00/0.99      ( X0 = X1
% 3.00/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4222,plain,
% 3.00/0.99      ( g1_orders_2(X0,X1) != k3_lattice3(sK1)
% 3.00/0.99      | k8_filter_1(sK1) = X1
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4217,c_1682]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_32,plain,
% 3.00/0.99      ( v10_lattices(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_15,plain,
% 3.00/0.99      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1675,plain,
% 3.00/0.99      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2600,plain,
% 3.00/0.99      ( m1_subset_1(k8_filter_1(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2286,c_1675]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4223,plain,
% 3.00/0.99      ( g1_orders_2(X0,X1) != k3_lattice3(sK1)
% 3.00/0.99      | k8_filter_1(sK1) = X1
% 3.00/0.99      | m1_subset_1(k8_filter_1(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4217,c_1682]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4868,plain,
% 3.00/0.99      ( k8_filter_1(sK1) = X1 | g1_orders_2(X0,X1) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_4222,c_31,c_32,c_33,c_2600,c_4223]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4869,plain,
% 3.00/0.99      ( g1_orders_2(X0,X1) != k3_lattice3(sK1) | k8_filter_1(sK1) = X1 ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_4868]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4873,plain,
% 3.00/0.99      ( u1_orders_2(k3_lattice3(sK1)) = k8_filter_1(sK1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3522,c_4869]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_11,plain,
% 3.00/0.99      ( ~ r3_lattices(X0,X1,X2)
% 3.00/0.99      | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3,plain,
% 3.00/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.00/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ l1_orders_2(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_25,negated_conjecture,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_228,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
% 3.00/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_8,plain,
% 3.00/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.00/0.99      | r1_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ v3_orders_2(X0)
% 3.00/0.99      | ~ l1_orders_2(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_17,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v3_orders_2(k3_lattice3(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_425,plain,
% 3.00/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.00/0.99      | r1_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | ~ l1_orders_2(X0)
% 3.00/0.99      | k3_lattice3(X3) != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_426,plain,
% 3.00/0.99      ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(k3_lattice3(X0))
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_22,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ v2_struct_0(k3_lattice3(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_430,plain,
% 3.00/0.99      ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_426,c_22,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_577,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k4_lattice3(sK1,sK3) != X2
% 3.00/0.99      | k4_lattice3(sK1,sK2) != X1
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_228,c_430]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_578,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r1_orders_2(k3_lattice3(X0),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_577]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_777,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 3.00/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | ~ l1_orders_2(X2)
% 3.00/0.99      | k4_lattice3(sK1,sK3) != X1
% 3.00/0.99      | k4_lattice3(sK1,sK2) != X0
% 3.00/0.99      | k3_lattice3(X3) != X2
% 3.00/0.99      | k3_lattice3(X3) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_578]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_778,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(X0))
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_777]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_782,plain,
% 3.00/0.99      ( v2_struct_0(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,[status(thm)],[c_778,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_783,plain,
% 3.00/0.99      ( r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_782]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1015,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | k3_lattice3(X3) != k3_lattice3(sK1)
% 3.00/0.99      | sK3 != X2
% 3.00/0.99      | sK2 != X1
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_783]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1016,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_1015]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_27,negated_conjecture,
% 3.00/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_26,negated_conjecture,
% 3.00/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1020,plain,
% 3.00/0.99      ( v2_struct_0(X0)
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1016,c_30,c_29,c_28,c_27,c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1021,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_1020]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1661,plain,
% 3.00/0.99      ( k3_lattice3(X0) != k3_lattice3(sK1)
% 3.00/0.99      | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0))) = iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0))) != iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0))) != iProver_top
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1999,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) != iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) != iProver_top
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(equality_resolution,[status(thm)],[c_1661]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_34,plain,
% 3.00/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_35,plain,
% 3.00/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_19,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/0.99      | m1_subset_1(k4_lattice3(X1,X0),u1_struct_0(k3_lattice3(X1)))
% 3.00/0.99      | ~ v10_lattices(X1)
% 3.00/0.99      | ~ l3_lattices(X1)
% 3.00/0.99      | v2_struct_0(X1) ),
% 3.00/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1932,plain,
% 3.00/0.99      ( m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1)))
% 3.00/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1933,plain,
% 3.00/0.99      ( m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) = iProver_top
% 3.00/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1935,plain,
% 3.00/0.99      ( m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1)))
% 3.00/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1936,plain,
% 3.00/0.99      ( m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) = iProver_top
% 3.00/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1935]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3888,plain,
% 3.00/0.99      ( r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top
% 3.00/0.99      | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_1999,c_31,c_32,c_33,c_34,c_35,c_1933,c_1936]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3889,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) = iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) = iProver_top ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_3888]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1671,plain,
% 3.00/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_14,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/0.99      | ~ v10_lattices(X1)
% 3.00/0.99      | ~ l3_lattices(X1)
% 3.00/0.99      | v2_struct_0(X1)
% 3.00/0.99      | k4_lattice3(X1,X0) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1676,plain,
% 3.00/0.99      ( k4_lattice3(X0,X1) = X1
% 3.00/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2751,plain,
% 3.00/0.99      ( k4_lattice3(sK1,sK3) = sK3
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1671,c_1676]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1926,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | k4_lattice3(sK1,sK3) = sK3 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2856,plain,
% 3.00/0.99      ( k4_lattice3(sK1,sK3) = sK3 ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_2751,c_30,c_29,c_28,c_26,c_1926]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1670,plain,
% 3.00/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2752,plain,
% 3.00/0.99      ( k4_lattice3(sK1,sK2) = sK2
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1670,c_1676]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1929,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | k4_lattice3(sK1,sK2) = sK2 ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2948,plain,
% 3.00/0.99      ( k4_lattice3(sK1,sK2) = sK2 ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_2752,c_30,c_29,c_28,c_27,c_1929]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,X1)
% 3.00/0.99      | ~ m1_subset_1(X2,X3)
% 3.00/0.99      | v1_xboole_0(X3)
% 3.00/0.99      | v1_xboole_0(X1)
% 3.00/0.99      | k1_domain_1(X3,X1,X2,X0) = k4_tarski(X2,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1680,plain,
% 3.00/0.99      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
% 3.00/0.99      | m1_subset_1(X3,X1) != iProver_top
% 3.00/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.00/0.99      | v1_xboole_0(X0) = iProver_top
% 3.00/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2779,plain,
% 3.00/0.99      ( k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3)
% 3.00/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.00/0.99      | v1_xboole_0(X0) = iProver_top
% 3.00/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1671,c_1680]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_10,plain,
% 3.00/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_73,plain,
% 3.00/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_75,plain,
% 3.00/0.99      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.00/0.99      | v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_73]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_9,plain,
% 3.00/0.99      ( ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ v1_xboole_0(sK0(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_76,plain,
% 3.00/0.99      ( v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top
% 3.00/0.99      | v1_xboole_0(sK0(X0)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_78,plain,
% 3.00/0.99      ( v10_lattices(sK1) != iProver_top
% 3.00/0.99      | l3_lattices(sK1) != iProver_top
% 3.00/0.99      | v2_struct_0(sK1) = iProver_top
% 3.00/0.99      | v1_xboole_0(sK0(sK1)) != iProver_top ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_76]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_0,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.99      | ~ v1_xboole_0(X1)
% 3.00/0.99      | v1_xboole_0(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2164,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.00/0.99      | v1_xboole_0(X0)
% 3.00/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2556,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.00/0.99      | v1_xboole_0(sK0(sK1))
% 3.00/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_2164]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2558,plain,
% 3.00/0.99      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.00/0.99      | v1_xboole_0(sK0(sK1)) = iProver_top
% 3.00/0.99      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3004,plain,
% 3.00/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.00/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.00/0.99      | k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_2779,c_31,c_32,c_33,c_75,c_78,c_2558]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3005,plain,
% 3.00/0.99      ( k1_domain_1(X0,u1_struct_0(sK1),X1,sK3) = k4_tarski(X1,sK3)
% 3.00/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.00/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_3004]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3016,plain,
% 3.00/0.99      ( k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3)
% 3.00/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1670,c_3005]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_74,plain,
% 3.00/0.99      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_77,plain,
% 3.00/0.99      ( ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | ~ v1_xboole_0(sK0(sK1)) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1974,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,X1)
% 3.00/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | v1_xboole_0(X1)
% 3.00/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 3.00/0.99      | k1_domain_1(X1,u1_struct_0(sK1),X0,sK3) = k4_tarski(X0,sK3) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2092,plain,
% 3.00/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.00/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 3.00/0.99      | k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3) ),
% 3.00/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3154,plain,
% 3.00/0.99      ( k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3) = k4_tarski(sK2,sK3) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_3016,c_30,c_29,c_28,c_27,c_26,c_74,c_77,c_2092,c_2556]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3892,plain,
% 3.00/0.99      ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) = iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(k3_lattice3(sK1))) = iProver_top ),
% 3.00/0.99      inference(light_normalisation,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_3889,c_2856,c_2948,c_3154]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5076,plain,
% 3.00/0.99      ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) = iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_4873,c_3892]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_12,plain,
% 3.00/0.99      ( r3_lattices(X0,X1,X2)
% 3.00/0.99      | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2,plain,
% 3.00/0.99      ( r1_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ l1_orders_2(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_24,negated_conjecture,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_226,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)) ),
% 3.00/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7,plain,
% 3.00/0.99      ( r3_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ v3_orders_2(X0)
% 3.00/0.99      | ~ l1_orders_2(X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_458,plain,
% 3.00/0.99      ( r3_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ r1_orders_2(X0,X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | ~ l1_orders_2(X0)
% 3.00/0.99      | k3_lattice3(X3) != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_459,plain,
% 3.00/0.99      ( r3_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(k3_lattice3(X0))
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(X0)) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_458]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_463,plain,
% 3.00/0.99      ( r3_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_459,c_22,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_607,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r1_orders_2(k3_lattice3(X0),X1,X2)
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k4_lattice3(sK1,sK3) != X2
% 3.00/0.99      | k4_lattice3(sK1,sK2) != X1
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_226,c_463]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_608,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r1_orders_2(k3_lattice3(X0),k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_607]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_741,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X2))
% 3.00/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | ~ l1_orders_2(X2)
% 3.00/0.99      | k4_lattice3(sK1,sK3) != X1
% 3.00/0.99      | k4_lattice3(sK1,sK2) != X0
% 3.00/0.99      | k3_lattice3(X3) != X2
% 3.00/0.99      | k3_lattice3(X3) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_608]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_742,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | ~ l1_orders_2(k3_lattice3(X0))
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_741]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_746,plain,
% 3.00/0.99      ( v2_struct_0(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,[status(thm)],[c_742,c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_747,plain,
% 3.00/0.99      ( ~ r3_lattices(sK1,sK2,sK3)
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_746]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_979,plain,
% 3.00/0.99      ( ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X3)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(X3)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X3)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(X3)
% 3.00/0.99      | k3_lattice3(X3) != k3_lattice3(sK1)
% 3.00/0.99      | sK3 != X2
% 3.00/0.99      | sK2 != X1
% 3.00/0.99      | sK1 != X0 ),
% 3.00/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_747]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_980,plain,
% 3.00/0.99      ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 3.00/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ v10_lattices(sK1)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(sK1)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | v2_struct_0(sK1)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(unflattening,[status(thm)],[c_979]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_984,plain,
% 3.00/0.99      ( v2_struct_0(X0)
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(global_propositional_subsumption,
% 3.00/0.99                [status(thm)],
% 3.00/0.99                [c_980,c_30,c_29,c_28,c_27,c_26]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_985,plain,
% 3.00/0.99      ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1))
% 3.00/0.99      | ~ r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0)))
% 3.00/0.99      | ~ v10_lattices(X0)
% 3.00/0.99      | ~ l3_lattices(X0)
% 3.00/0.99      | v2_struct_0(X0)
% 3.00/0.99      | k3_lattice3(X0) != k3_lattice3(sK1) ),
% 3.00/0.99      inference(renaming,[status(thm)],[c_984]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1662,plain,
% 3.00/0.99      ( k3_lattice3(X0) != k3_lattice3(sK1)
% 3.00/0.99      | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
% 3.00/0.99      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(X0))) != iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(X0))) != iProver_top
% 3.00/0.99      | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(X0))) != iProver_top
% 3.00/0.99      | v10_lattices(X0) != iProver_top
% 3.00/0.99      | l3_lattices(X0) != iProver_top
% 3.00/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2436,plain,
% 3.00/0.99      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
% 3.00/1.00      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top
% 3.00/1.00      | m1_subset_1(k4_lattice3(sK1,sK3),u1_struct_0(k3_lattice3(sK1))) != iProver_top
% 3.00/1.00      | m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) != iProver_top
% 3.00/1.00      | v10_lattices(sK1) != iProver_top
% 3.00/1.00      | l3_lattices(sK1) != iProver_top
% 3.00/1.00      | v2_struct_0(sK1) = iProver_top ),
% 3.00/1.00      inference(equality_resolution,[status(thm)],[c_1662]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2512,plain,
% 3.00/1.00      ( r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top
% 3.00/1.00      | r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_2436,c_31,c_32,c_33,c_34,c_35,c_1933,c_1936]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2513,plain,
% 3.00/1.00      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
% 3.00/1.00      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),k4_lattice3(sK1,sK3)),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_2512]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2860,plain,
% 3.00/1.00      ( r2_hidden(k1_domain_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2,sK3),k8_filter_1(sK1)) != iProver_top
% 3.00/1.00      | r2_hidden(k4_tarski(k4_lattice3(sK1,sK2),sK3),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_2856,c_2513]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3801,plain,
% 3.00/1.00      ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) != iProver_top
% 3.00/1.00      | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(k3_lattice3(sK1))) != iProver_top ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_2860,c_2948,c_3154]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5077,plain,
% 3.00/1.00      ( r2_hidden(k4_tarski(sK2,sK3),k8_filter_1(sK1)) != iProver_top ),
% 3.00/1.00      inference(demodulation,[status(thm)],[c_4873,c_3801]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5087,plain,
% 3.00/1.00      ( $false ),
% 3.00/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5076,c_5077]) ).
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  ------                               Statistics
% 3.00/1.00  
% 3.00/1.00  ------ General
% 3.00/1.00  
% 3.00/1.00  abstr_ref_over_cycles:                  0
% 3.00/1.00  abstr_ref_under_cycles:                 0
% 3.00/1.00  gc_basic_clause_elim:                   0
% 3.00/1.00  forced_gc_time:                         0
% 3.00/1.00  parsing_time:                           0.014
% 3.00/1.00  unif_index_cands_time:                  0.
% 3.00/1.00  unif_index_add_time:                    0.
% 3.00/1.00  orderings_time:                         0.
% 3.00/1.00  out_proof_time:                         0.018
% 3.00/1.00  total_time:                             0.204
% 3.00/1.00  num_of_symbols:                         60
% 3.00/1.00  num_of_terms:                           3997
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing
% 3.00/1.00  
% 3.00/1.00  num_of_splits:                          2
% 3.00/1.00  num_of_split_atoms:                     2
% 3.00/1.00  num_of_reused_defs:                     0
% 3.00/1.00  num_eq_ax_congr_red:                    15
% 3.00/1.00  num_of_sem_filtered_clauses:            1
% 3.00/1.00  num_of_subtypes:                        0
% 3.00/1.00  monotx_restored_types:                  0
% 3.00/1.00  sat_num_of_epr_types:                   0
% 3.00/1.00  sat_num_of_non_cyclic_types:            0
% 3.00/1.00  sat_guarded_non_collapsed_types:        0
% 3.00/1.00  num_pure_diseq_elim:                    0
% 3.00/1.00  simp_replaced_by:                       0
% 3.00/1.00  res_preprocessed:                       133
% 3.00/1.00  prep_upred:                             0
% 3.00/1.00  prep_unflattend:                        21
% 3.00/1.00  smt_new_axioms:                         0
% 3.00/1.00  pred_elim_cands:                        6
% 3.00/1.00  pred_elim:                              6
% 3.00/1.00  pred_elim_cl:                           8
% 3.00/1.00  pred_elim_cycles:                       11
% 3.00/1.00  merged_defs:                            2
% 3.00/1.00  merged_defs_ncl:                        0
% 3.00/1.00  bin_hyper_res:                          2
% 3.00/1.00  prep_cycles:                            4
% 3.00/1.00  pred_elim_time:                         0.019
% 3.00/1.00  splitting_time:                         0.
% 3.00/1.00  sem_filter_time:                        0.
% 3.00/1.00  monotx_time:                            0.
% 3.00/1.00  subtype_inf_time:                       0.
% 3.00/1.00  
% 3.00/1.00  ------ Problem properties
% 3.00/1.00  
% 3.00/1.00  clauses:                                23
% 3.00/1.00  conjectures:                            5
% 3.00/1.00  epr:                                    4
% 3.00/1.00  horn:                                   12
% 3.00/1.00  ground:                                 6
% 3.00/1.00  unary:                                  5
% 3.00/1.00  binary:                                 1
% 3.00/1.00  lits:                                   91
% 3.00/1.00  lits_eq:                                13
% 3.00/1.00  fd_pure:                                0
% 3.00/1.00  fd_pseudo:                              0
% 3.00/1.00  fd_cond:                                0
% 3.00/1.00  fd_pseudo_cond:                         2
% 3.00/1.00  ac_symbols:                             0
% 3.00/1.00  
% 3.00/1.00  ------ Propositional Solver
% 3.00/1.00  
% 3.00/1.00  prop_solver_calls:                      28
% 3.00/1.00  prop_fast_solver_calls:                 1473
% 3.00/1.00  smt_solver_calls:                       0
% 3.00/1.00  smt_fast_solver_calls:                  0
% 3.00/1.00  prop_num_of_clauses:                    1616
% 3.00/1.00  prop_preprocess_simplified:             5695
% 3.00/1.00  prop_fo_subsumed:                       69
% 3.00/1.00  prop_solver_time:                       0.
% 3.00/1.00  smt_solver_time:                        0.
% 3.00/1.00  smt_fast_solver_time:                   0.
% 3.00/1.00  prop_fast_solver_time:                  0.
% 3.00/1.00  prop_unsat_core_time:                   0.
% 3.00/1.00  
% 3.00/1.00  ------ QBF
% 3.00/1.00  
% 3.00/1.00  qbf_q_res:                              0
% 3.00/1.00  qbf_num_tautologies:                    0
% 3.00/1.00  qbf_prep_cycles:                        0
% 3.00/1.00  
% 3.00/1.00  ------ BMC1
% 3.00/1.00  
% 3.00/1.00  bmc1_current_bound:                     -1
% 3.00/1.00  bmc1_last_solved_bound:                 -1
% 3.00/1.00  bmc1_unsat_core_size:                   -1
% 3.00/1.00  bmc1_unsat_core_parents_size:           -1
% 3.00/1.00  bmc1_merge_next_fun:                    0
% 3.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation
% 3.00/1.00  
% 3.00/1.00  inst_num_of_clauses:                    494
% 3.00/1.00  inst_num_in_passive:                    84
% 3.00/1.00  inst_num_in_active:                     283
% 3.00/1.00  inst_num_in_unprocessed:                127
% 3.00/1.00  inst_num_of_loops:                      310
% 3.00/1.00  inst_num_of_learning_restarts:          0
% 3.00/1.00  inst_num_moves_active_passive:          24
% 3.00/1.00  inst_lit_activity:                      0
% 3.00/1.00  inst_lit_activity_moves:                0
% 3.00/1.00  inst_num_tautologies:                   0
% 3.00/1.00  inst_num_prop_implied:                  0
% 3.00/1.00  inst_num_existing_simplified:           0
% 3.00/1.00  inst_num_eq_res_simplified:             0
% 3.00/1.00  inst_num_child_elim:                    0
% 3.00/1.00  inst_num_of_dismatching_blockings:      58
% 3.00/1.00  inst_num_of_non_proper_insts:           560
% 3.00/1.00  inst_num_of_duplicates:                 0
% 3.00/1.00  inst_inst_num_from_inst_to_res:         0
% 3.00/1.00  inst_dismatching_checking_time:         0.
% 3.00/1.00  
% 3.00/1.00  ------ Resolution
% 3.00/1.00  
% 3.00/1.00  res_num_of_clauses:                     0
% 3.00/1.00  res_num_in_passive:                     0
% 3.00/1.00  res_num_in_active:                      0
% 3.00/1.00  res_num_of_loops:                       137
% 3.00/1.00  res_forward_subset_subsumed:            24
% 3.00/1.00  res_backward_subset_subsumed:           0
% 3.00/1.00  res_forward_subsumed:                   0
% 3.00/1.00  res_backward_subsumed:                  0
% 3.00/1.00  res_forward_subsumption_resolution:     0
% 3.00/1.00  res_backward_subsumption_resolution:    0
% 3.00/1.00  res_clause_to_clause_subsumption:       195
% 3.00/1.00  res_orphan_elimination:                 0
% 3.00/1.00  res_tautology_del:                      60
% 3.00/1.00  res_num_eq_res_simplified:              0
% 3.00/1.00  res_num_sel_changes:                    0
% 3.00/1.00  res_moves_from_active_to_pass:          0
% 3.00/1.00  
% 3.00/1.00  ------ Superposition
% 3.00/1.00  
% 3.00/1.00  sup_time_total:                         0.
% 3.00/1.00  sup_time_generating:                    0.
% 3.00/1.00  sup_time_sim_full:                      0.
% 3.00/1.00  sup_time_sim_immed:                     0.
% 3.00/1.00  
% 3.00/1.00  sup_num_of_clauses:                     77
% 3.00/1.00  sup_num_in_active:                      40
% 3.00/1.00  sup_num_in_passive:                     37
% 3.00/1.00  sup_num_of_loops:                       60
% 3.00/1.00  sup_fw_superposition:                   28
% 3.00/1.00  sup_bw_superposition:                   45
% 3.00/1.00  sup_immediate_simplified:               4
% 3.00/1.00  sup_given_eliminated:                   0
% 3.00/1.00  comparisons_done:                       0
% 3.00/1.00  comparisons_avoided:                    0
% 3.00/1.00  
% 3.00/1.00  ------ Simplifications
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  sim_fw_subset_subsumed:                 2
% 3.00/1.00  sim_bw_subset_subsumed:                 7
% 3.00/1.00  sim_fw_subsumed:                        1
% 3.00/1.00  sim_bw_subsumed:                        0
% 3.00/1.00  sim_fw_subsumption_res:                 1
% 3.00/1.00  sim_bw_subsumption_res:                 0
% 3.00/1.00  sim_tautology_del:                      1
% 3.00/1.00  sim_eq_tautology_del:                   6
% 3.00/1.00  sim_eq_res_simp:                        0
% 3.00/1.00  sim_fw_demodulated:                     0
% 3.00/1.00  sim_bw_demodulated:                     20
% 3.00/1.00  sim_light_normalised:                   7
% 3.00/1.00  sim_joinable_taut:                      0
% 3.00/1.00  sim_joinable_simp:                      0
% 3.00/1.00  sim_ac_normalised:                      0
% 3.00/1.00  sim_smt_subsumption:                    0
% 3.00/1.00  
%------------------------------------------------------------------------------
