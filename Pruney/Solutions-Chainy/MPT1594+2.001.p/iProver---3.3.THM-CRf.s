%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:04 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  172 (1730 expanded)
%              Number of clauses        :   92 ( 628 expanded)
%              Number of leaves         :   17 ( 304 expanded)
%              Depth                    :   26
%              Number of atoms          :  688 (4924 expanded)
%              Number of equality atoms :  113 ( 711 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f69,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f68,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f66,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(flattening,[],[f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
     => ( ( ~ r1_tarski(X1,sK2)
          | ~ r3_orders_2(k3_yellow_1(X0),X1,sK2) )
        & ( r1_tarski(X1,sK2)
          | r3_orders_2(k3_yellow_1(X0),X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r3_orders_2(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
          & ( r1_tarski(sK1,X2)
            | r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f51,f50])).

fof(f75,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f75,f74])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_lattices(k1_lattice3(X0),X1,X2)
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_lattices(k1_lattice3(X0),X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(k1_lattice3(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_lattices(X0,X1,X2)
                  | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f77,f74])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f78,f74])).

cnf(c_14,plain,
    ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,plain,
    ( v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_713,plain,
    ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_714,plain,
    ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0)))))
    | ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_15,plain,
    ( ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_718,plain,
    ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_15,c_13])).

cnf(c_1857,plain,
    ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1865,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2232,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1865])).

cnf(c_11,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_728,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_729,plain,
    ( ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0))
    | g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) = k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_733,plain,
    ( g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) = k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_15,c_13])).

cnf(c_2233,plain,
    ( l1_orders_2(k3_lattice3(k1_lattice3(X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2232,c_733])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1866,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2389,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) = k3_lattice3(k1_lattice3(X0))
    | v1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_1866])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2224,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1864])).

cnf(c_2225,plain,
    ( v1_orders_2(k3_lattice3(k1_lattice3(X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2224,c_733])).

cnf(c_2468,plain,
    ( g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) = k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_2225])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1862,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2290,plain,
    ( g1_orders_2(X0,X1) != k3_lattice3(k1_lattice3(X2))
    | u1_struct_0(k1_lattice3(X2)) = X0
    | m1_subset_1(k2_lattice3(k1_lattice3(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X2)),u1_struct_0(k1_lattice3(X2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_1862])).

cnf(c_2839,plain,
    ( g1_orders_2(X0,X1) != k3_lattice3(k1_lattice3(X2))
    | u1_struct_0(k1_lattice3(X2)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2290,c_1857])).

cnf(c_2842,plain,
    ( k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = u1_struct_0(k1_lattice3(X0)) ),
    inference(superposition,[status(thm)],[c_2468,c_2839])).

cnf(c_3161,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) = u1_struct_0(k1_lattice3(X0)) ),
    inference(equality_resolution,[status(thm)],[c_2842])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1858,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3256,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3161,c_1858])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattice3(X1,X0) = X0
    | k1_lattice3(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
    | ~ l3_lattices(k1_lattice3(X1))
    | v2_struct_0(k1_lattice3(X1))
    | k4_lattice3(k1_lattice3(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
    | k4_lattice3(k1_lattice3(X1),X0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_740,c_15,c_13])).

cnf(c_1856,plain,
    ( k4_lattice3(k1_lattice3(X0),X1) = X1
    | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_3341,plain,
    ( k4_lattice3(k1_lattice3(sK0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3256,c_1856])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1859,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3255,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3161,c_1859])).

cnf(c_3282,plain,
    ( k4_lattice3(k1_lattice3(sK0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3255,c_1856])).

cnf(c_17,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_477,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_7,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_481,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_7,c_6])).

cnf(c_617,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_16])).

cnf(c_618,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_15,c_13])).

cnf(c_623,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_20,plain,
    ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_665,plain,
    ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_16])).

cnf(c_666,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_670,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_15,c_13])).

cnf(c_671,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_670])).

cnf(c_870,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_623,c_671])).

cnf(c_984,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_17,c_870])).

cnf(c_1854,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_3346,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1854])).

cnf(c_4120,plain,
    ( m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3346,c_3255])).

cnf(c_4121,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4120])).

cnf(c_4130,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_4121])).

cnf(c_19,plain,
    ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_689,plain,
    ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_16])).

cnf(c_690,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_694,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_15,c_13])).

cnf(c_695,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_694])).

cnf(c_10,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_445,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_5,c_10])).

cnf(c_449,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_7,c_6])).

cnf(c_641,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_449,c_16])).

cnf(c_642,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ l3_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_646,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_15,c_13])).

cnf(c_647,plain,
    ( r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ r3_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_646])).

cnf(c_853,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | r1_lattices(k1_lattice3(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_695,c_647])).

cnf(c_18,plain,
    ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_967,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_853,c_18])).

cnf(c_1855,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_3345,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1855])).

cnf(c_3899,plain,
    ( m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3345,c_3255])).

cnf(c_3900,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3899])).

cnf(c_3909,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_3900])).

cnf(c_22,negated_conjecture,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3979,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3909,c_27,c_3256])).

cnf(c_21,negated_conjecture,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4130,c_3979,c_3256,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.56/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.02  
% 2.56/1.02  ------  iProver source info
% 2.56/1.02  
% 2.56/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.02  git: non_committed_changes: false
% 2.56/1.02  git: last_make_outside_of_git: false
% 2.56/1.02  
% 2.56/1.02  ------ 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options
% 2.56/1.02  
% 2.56/1.02  --out_options                           all
% 2.56/1.02  --tptp_safe_out                         true
% 2.56/1.02  --problem_path                          ""
% 2.56/1.02  --include_path                          ""
% 2.56/1.02  --clausifier                            res/vclausify_rel
% 2.56/1.02  --clausifier_options                    --mode clausify
% 2.56/1.02  --stdin                                 false
% 2.56/1.02  --stats_out                             all
% 2.56/1.02  
% 2.56/1.02  ------ General Options
% 2.56/1.02  
% 2.56/1.02  --fof                                   false
% 2.56/1.02  --time_out_real                         305.
% 2.56/1.02  --time_out_virtual                      -1.
% 2.56/1.02  --symbol_type_check                     false
% 2.56/1.02  --clausify_out                          false
% 2.56/1.02  --sig_cnt_out                           false
% 2.56/1.02  --trig_cnt_out                          false
% 2.56/1.02  --trig_cnt_out_tolerance                1.
% 2.56/1.02  --trig_cnt_out_sk_spl                   false
% 2.56/1.02  --abstr_cl_out                          false
% 2.56/1.02  
% 2.56/1.02  ------ Global Options
% 2.56/1.02  
% 2.56/1.02  --schedule                              default
% 2.56/1.02  --add_important_lit                     false
% 2.56/1.02  --prop_solver_per_cl                    1000
% 2.56/1.02  --min_unsat_core                        false
% 2.56/1.02  --soft_assumptions                      false
% 2.56/1.02  --soft_lemma_size                       3
% 2.56/1.02  --prop_impl_unit_size                   0
% 2.56/1.02  --prop_impl_unit                        []
% 2.56/1.02  --share_sel_clauses                     true
% 2.56/1.02  --reset_solvers                         false
% 2.56/1.02  --bc_imp_inh                            [conj_cone]
% 2.56/1.02  --conj_cone_tolerance                   3.
% 2.56/1.02  --extra_neg_conj                        none
% 2.56/1.02  --large_theory_mode                     true
% 2.56/1.02  --prolific_symb_bound                   200
% 2.56/1.02  --lt_threshold                          2000
% 2.56/1.02  --clause_weak_htbl                      true
% 2.56/1.02  --gc_record_bc_elim                     false
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing Options
% 2.56/1.02  
% 2.56/1.02  --preprocessing_flag                    true
% 2.56/1.02  --time_out_prep_mult                    0.1
% 2.56/1.02  --splitting_mode                        input
% 2.56/1.02  --splitting_grd                         true
% 2.56/1.02  --splitting_cvd                         false
% 2.56/1.02  --splitting_cvd_svl                     false
% 2.56/1.02  --splitting_nvd                         32
% 2.56/1.02  --sub_typing                            true
% 2.56/1.02  --prep_gs_sim                           true
% 2.56/1.02  --prep_unflatten                        true
% 2.56/1.02  --prep_res_sim                          true
% 2.56/1.02  --prep_upred                            true
% 2.56/1.02  --prep_sem_filter                       exhaustive
% 2.56/1.02  --prep_sem_filter_out                   false
% 2.56/1.02  --pred_elim                             true
% 2.56/1.02  --res_sim_input                         true
% 2.56/1.02  --eq_ax_congr_red                       true
% 2.56/1.02  --pure_diseq_elim                       true
% 2.56/1.02  --brand_transform                       false
% 2.56/1.02  --non_eq_to_eq                          false
% 2.56/1.02  --prep_def_merge                        true
% 2.56/1.02  --prep_def_merge_prop_impl              false
% 2.56/1.02  --prep_def_merge_mbd                    true
% 2.56/1.02  --prep_def_merge_tr_red                 false
% 2.56/1.02  --prep_def_merge_tr_cl                  false
% 2.56/1.02  --smt_preprocessing                     true
% 2.56/1.02  --smt_ac_axioms                         fast
% 2.56/1.02  --preprocessed_out                      false
% 2.56/1.02  --preprocessed_stats                    false
% 2.56/1.02  
% 2.56/1.02  ------ Abstraction refinement Options
% 2.56/1.02  
% 2.56/1.02  --abstr_ref                             []
% 2.56/1.02  --abstr_ref_prep                        false
% 2.56/1.02  --abstr_ref_until_sat                   false
% 2.56/1.02  --abstr_ref_sig_restrict                funpre
% 2.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.02  --abstr_ref_under                       []
% 2.56/1.02  
% 2.56/1.02  ------ SAT Options
% 2.56/1.02  
% 2.56/1.02  --sat_mode                              false
% 2.56/1.02  --sat_fm_restart_options                ""
% 2.56/1.02  --sat_gr_def                            false
% 2.56/1.02  --sat_epr_types                         true
% 2.56/1.02  --sat_non_cyclic_types                  false
% 2.56/1.02  --sat_finite_models                     false
% 2.56/1.02  --sat_fm_lemmas                         false
% 2.56/1.02  --sat_fm_prep                           false
% 2.56/1.02  --sat_fm_uc_incr                        true
% 2.56/1.02  --sat_out_model                         small
% 2.56/1.02  --sat_out_clauses                       false
% 2.56/1.02  
% 2.56/1.02  ------ QBF Options
% 2.56/1.02  
% 2.56/1.02  --qbf_mode                              false
% 2.56/1.02  --qbf_elim_univ                         false
% 2.56/1.02  --qbf_dom_inst                          none
% 2.56/1.02  --qbf_dom_pre_inst                      false
% 2.56/1.02  --qbf_sk_in                             false
% 2.56/1.02  --qbf_pred_elim                         true
% 2.56/1.02  --qbf_split                             512
% 2.56/1.02  
% 2.56/1.02  ------ BMC1 Options
% 2.56/1.02  
% 2.56/1.02  --bmc1_incremental                      false
% 2.56/1.02  --bmc1_axioms                           reachable_all
% 2.56/1.02  --bmc1_min_bound                        0
% 2.56/1.02  --bmc1_max_bound                        -1
% 2.56/1.02  --bmc1_max_bound_default                -1
% 2.56/1.02  --bmc1_symbol_reachability              true
% 2.56/1.02  --bmc1_property_lemmas                  false
% 2.56/1.02  --bmc1_k_induction                      false
% 2.56/1.02  --bmc1_non_equiv_states                 false
% 2.56/1.02  --bmc1_deadlock                         false
% 2.56/1.02  --bmc1_ucm                              false
% 2.56/1.02  --bmc1_add_unsat_core                   none
% 2.56/1.02  --bmc1_unsat_core_children              false
% 2.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.02  --bmc1_out_stat                         full
% 2.56/1.02  --bmc1_ground_init                      false
% 2.56/1.02  --bmc1_pre_inst_next_state              false
% 2.56/1.02  --bmc1_pre_inst_state                   false
% 2.56/1.02  --bmc1_pre_inst_reach_state             false
% 2.56/1.02  --bmc1_out_unsat_core                   false
% 2.56/1.02  --bmc1_aig_witness_out                  false
% 2.56/1.02  --bmc1_verbose                          false
% 2.56/1.02  --bmc1_dump_clauses_tptp                false
% 2.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.02  --bmc1_dump_file                        -
% 2.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.02  --bmc1_ucm_extend_mode                  1
% 2.56/1.02  --bmc1_ucm_init_mode                    2
% 2.56/1.02  --bmc1_ucm_cone_mode                    none
% 2.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.02  --bmc1_ucm_relax_model                  4
% 2.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.02  --bmc1_ucm_layered_model                none
% 2.56/1.02  --bmc1_ucm_max_lemma_size               10
% 2.56/1.02  
% 2.56/1.02  ------ AIG Options
% 2.56/1.02  
% 2.56/1.02  --aig_mode                              false
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation Options
% 2.56/1.02  
% 2.56/1.02  --instantiation_flag                    true
% 2.56/1.02  --inst_sos_flag                         false
% 2.56/1.02  --inst_sos_phase                        true
% 2.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel_side                     num_symb
% 2.56/1.02  --inst_solver_per_active                1400
% 2.56/1.02  --inst_solver_calls_frac                1.
% 2.56/1.02  --inst_passive_queue_type               priority_queues
% 2.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.02  --inst_passive_queues_freq              [25;2]
% 2.56/1.02  --inst_dismatching                      true
% 2.56/1.02  --inst_eager_unprocessed_to_passive     true
% 2.56/1.02  --inst_prop_sim_given                   true
% 2.56/1.02  --inst_prop_sim_new                     false
% 2.56/1.02  --inst_subs_new                         false
% 2.56/1.02  --inst_eq_res_simp                      false
% 2.56/1.02  --inst_subs_given                       false
% 2.56/1.02  --inst_orphan_elimination               true
% 2.56/1.02  --inst_learning_loop_flag               true
% 2.56/1.02  --inst_learning_start                   3000
% 2.56/1.02  --inst_learning_factor                  2
% 2.56/1.02  --inst_start_prop_sim_after_learn       3
% 2.56/1.02  --inst_sel_renew                        solver
% 2.56/1.02  --inst_lit_activity_flag                true
% 2.56/1.02  --inst_restr_to_given                   false
% 2.56/1.02  --inst_activity_threshold               500
% 2.56/1.02  --inst_out_proof                        true
% 2.56/1.02  
% 2.56/1.02  ------ Resolution Options
% 2.56/1.02  
% 2.56/1.02  --resolution_flag                       true
% 2.56/1.02  --res_lit_sel                           adaptive
% 2.56/1.02  --res_lit_sel_side                      none
% 2.56/1.02  --res_ordering                          kbo
% 2.56/1.02  --res_to_prop_solver                    active
% 2.56/1.02  --res_prop_simpl_new                    false
% 2.56/1.02  --res_prop_simpl_given                  true
% 2.56/1.02  --res_passive_queue_type                priority_queues
% 2.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.02  --res_passive_queues_freq               [15;5]
% 2.56/1.02  --res_forward_subs                      full
% 2.56/1.02  --res_backward_subs                     full
% 2.56/1.02  --res_forward_subs_resolution           true
% 2.56/1.02  --res_backward_subs_resolution          true
% 2.56/1.02  --res_orphan_elimination                true
% 2.56/1.02  --res_time_limit                        2.
% 2.56/1.02  --res_out_proof                         true
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Options
% 2.56/1.02  
% 2.56/1.02  --superposition_flag                    true
% 2.56/1.02  --sup_passive_queue_type                priority_queues
% 2.56/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.02  --demod_completeness_check              fast
% 2.56/1.02  --demod_use_ground                      true
% 2.56/1.02  --sup_to_prop_solver                    passive
% 2.56/1.02  --sup_prop_simpl_new                    true
% 2.56/1.02  --sup_prop_simpl_given                  true
% 2.56/1.02  --sup_fun_splitting                     false
% 2.56/1.02  --sup_smt_interval                      50000
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Simplification Setup
% 2.56/1.02  
% 2.56/1.02  --sup_indices_passive                   []
% 2.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_full_bw                           [BwDemod]
% 2.56/1.02  --sup_immed_triv                        [TrivRules]
% 2.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_immed_bw_main                     []
% 2.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  
% 2.56/1.02  ------ Combination Options
% 2.56/1.02  
% 2.56/1.02  --comb_res_mult                         3
% 2.56/1.02  --comb_sup_mult                         2
% 2.56/1.02  --comb_inst_mult                        10
% 2.56/1.02  
% 2.56/1.02  ------ Debug Options
% 2.56/1.02  
% 2.56/1.02  --dbg_backtrace                         false
% 2.56/1.02  --dbg_dump_prop_clauses                 false
% 2.56/1.02  --dbg_dump_prop_clauses_file            -
% 2.56/1.02  --dbg_out_stat                          false
% 2.56/1.02  ------ Parsing...
% 2.56/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.02  ------ Proving...
% 2.56/1.02  ------ Problem Properties 
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  clauses                                 14
% 2.56/1.02  conjectures                             4
% 2.56/1.02  EPR                                     0
% 2.56/1.02  Horn                                    13
% 2.56/1.02  unary                                   4
% 2.56/1.02  binary                                  5
% 2.56/1.02  lits                                    31
% 2.56/1.02  lits eq                                 7
% 2.56/1.02  fd_pure                                 0
% 2.56/1.02  fd_pseudo                               0
% 2.56/1.02  fd_cond                                 0
% 2.56/1.02  fd_pseudo_cond                          2
% 2.56/1.02  AC symbols                              0
% 2.56/1.02  
% 2.56/1.02  ------ Schedule dynamic 5 is on 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  ------ 
% 2.56/1.02  Current options:
% 2.56/1.02  ------ 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options
% 2.56/1.02  
% 2.56/1.02  --out_options                           all
% 2.56/1.02  --tptp_safe_out                         true
% 2.56/1.02  --problem_path                          ""
% 2.56/1.02  --include_path                          ""
% 2.56/1.02  --clausifier                            res/vclausify_rel
% 2.56/1.02  --clausifier_options                    --mode clausify
% 2.56/1.02  --stdin                                 false
% 2.56/1.02  --stats_out                             all
% 2.56/1.02  
% 2.56/1.02  ------ General Options
% 2.56/1.02  
% 2.56/1.02  --fof                                   false
% 2.56/1.02  --time_out_real                         305.
% 2.56/1.02  --time_out_virtual                      -1.
% 2.56/1.02  --symbol_type_check                     false
% 2.56/1.02  --clausify_out                          false
% 2.56/1.02  --sig_cnt_out                           false
% 2.56/1.02  --trig_cnt_out                          false
% 2.56/1.02  --trig_cnt_out_tolerance                1.
% 2.56/1.02  --trig_cnt_out_sk_spl                   false
% 2.56/1.02  --abstr_cl_out                          false
% 2.56/1.02  
% 2.56/1.02  ------ Global Options
% 2.56/1.02  
% 2.56/1.02  --schedule                              default
% 2.56/1.02  --add_important_lit                     false
% 2.56/1.02  --prop_solver_per_cl                    1000
% 2.56/1.02  --min_unsat_core                        false
% 2.56/1.02  --soft_assumptions                      false
% 2.56/1.02  --soft_lemma_size                       3
% 2.56/1.02  --prop_impl_unit_size                   0
% 2.56/1.02  --prop_impl_unit                        []
% 2.56/1.02  --share_sel_clauses                     true
% 2.56/1.02  --reset_solvers                         false
% 2.56/1.02  --bc_imp_inh                            [conj_cone]
% 2.56/1.02  --conj_cone_tolerance                   3.
% 2.56/1.02  --extra_neg_conj                        none
% 2.56/1.02  --large_theory_mode                     true
% 2.56/1.02  --prolific_symb_bound                   200
% 2.56/1.02  --lt_threshold                          2000
% 2.56/1.02  --clause_weak_htbl                      true
% 2.56/1.02  --gc_record_bc_elim                     false
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing Options
% 2.56/1.02  
% 2.56/1.02  --preprocessing_flag                    true
% 2.56/1.02  --time_out_prep_mult                    0.1
% 2.56/1.02  --splitting_mode                        input
% 2.56/1.02  --splitting_grd                         true
% 2.56/1.02  --splitting_cvd                         false
% 2.56/1.02  --splitting_cvd_svl                     false
% 2.56/1.02  --splitting_nvd                         32
% 2.56/1.02  --sub_typing                            true
% 2.56/1.02  --prep_gs_sim                           true
% 2.56/1.02  --prep_unflatten                        true
% 2.56/1.02  --prep_res_sim                          true
% 2.56/1.02  --prep_upred                            true
% 2.56/1.02  --prep_sem_filter                       exhaustive
% 2.56/1.02  --prep_sem_filter_out                   false
% 2.56/1.02  --pred_elim                             true
% 2.56/1.02  --res_sim_input                         true
% 2.56/1.02  --eq_ax_congr_red                       true
% 2.56/1.02  --pure_diseq_elim                       true
% 2.56/1.02  --brand_transform                       false
% 2.56/1.02  --non_eq_to_eq                          false
% 2.56/1.02  --prep_def_merge                        true
% 2.56/1.02  --prep_def_merge_prop_impl              false
% 2.56/1.02  --prep_def_merge_mbd                    true
% 2.56/1.02  --prep_def_merge_tr_red                 false
% 2.56/1.02  --prep_def_merge_tr_cl                  false
% 2.56/1.02  --smt_preprocessing                     true
% 2.56/1.02  --smt_ac_axioms                         fast
% 2.56/1.02  --preprocessed_out                      false
% 2.56/1.02  --preprocessed_stats                    false
% 2.56/1.02  
% 2.56/1.02  ------ Abstraction refinement Options
% 2.56/1.02  
% 2.56/1.02  --abstr_ref                             []
% 2.56/1.02  --abstr_ref_prep                        false
% 2.56/1.02  --abstr_ref_until_sat                   false
% 2.56/1.02  --abstr_ref_sig_restrict                funpre
% 2.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.02  --abstr_ref_under                       []
% 2.56/1.02  
% 2.56/1.02  ------ SAT Options
% 2.56/1.02  
% 2.56/1.02  --sat_mode                              false
% 2.56/1.02  --sat_fm_restart_options                ""
% 2.56/1.02  --sat_gr_def                            false
% 2.56/1.02  --sat_epr_types                         true
% 2.56/1.02  --sat_non_cyclic_types                  false
% 2.56/1.02  --sat_finite_models                     false
% 2.56/1.02  --sat_fm_lemmas                         false
% 2.56/1.02  --sat_fm_prep                           false
% 2.56/1.02  --sat_fm_uc_incr                        true
% 2.56/1.02  --sat_out_model                         small
% 2.56/1.02  --sat_out_clauses                       false
% 2.56/1.02  
% 2.56/1.02  ------ QBF Options
% 2.56/1.02  
% 2.56/1.02  --qbf_mode                              false
% 2.56/1.02  --qbf_elim_univ                         false
% 2.56/1.02  --qbf_dom_inst                          none
% 2.56/1.02  --qbf_dom_pre_inst                      false
% 2.56/1.02  --qbf_sk_in                             false
% 2.56/1.02  --qbf_pred_elim                         true
% 2.56/1.02  --qbf_split                             512
% 2.56/1.02  
% 2.56/1.02  ------ BMC1 Options
% 2.56/1.02  
% 2.56/1.02  --bmc1_incremental                      false
% 2.56/1.02  --bmc1_axioms                           reachable_all
% 2.56/1.02  --bmc1_min_bound                        0
% 2.56/1.02  --bmc1_max_bound                        -1
% 2.56/1.02  --bmc1_max_bound_default                -1
% 2.56/1.02  --bmc1_symbol_reachability              true
% 2.56/1.02  --bmc1_property_lemmas                  false
% 2.56/1.02  --bmc1_k_induction                      false
% 2.56/1.02  --bmc1_non_equiv_states                 false
% 2.56/1.02  --bmc1_deadlock                         false
% 2.56/1.02  --bmc1_ucm                              false
% 2.56/1.02  --bmc1_add_unsat_core                   none
% 2.56/1.02  --bmc1_unsat_core_children              false
% 2.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.02  --bmc1_out_stat                         full
% 2.56/1.02  --bmc1_ground_init                      false
% 2.56/1.02  --bmc1_pre_inst_next_state              false
% 2.56/1.02  --bmc1_pre_inst_state                   false
% 2.56/1.02  --bmc1_pre_inst_reach_state             false
% 2.56/1.02  --bmc1_out_unsat_core                   false
% 2.56/1.02  --bmc1_aig_witness_out                  false
% 2.56/1.02  --bmc1_verbose                          false
% 2.56/1.02  --bmc1_dump_clauses_tptp                false
% 2.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.02  --bmc1_dump_file                        -
% 2.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.02  --bmc1_ucm_extend_mode                  1
% 2.56/1.02  --bmc1_ucm_init_mode                    2
% 2.56/1.02  --bmc1_ucm_cone_mode                    none
% 2.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.02  --bmc1_ucm_relax_model                  4
% 2.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.02  --bmc1_ucm_layered_model                none
% 2.56/1.02  --bmc1_ucm_max_lemma_size               10
% 2.56/1.02  
% 2.56/1.02  ------ AIG Options
% 2.56/1.02  
% 2.56/1.02  --aig_mode                              false
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation Options
% 2.56/1.02  
% 2.56/1.02  --instantiation_flag                    true
% 2.56/1.02  --inst_sos_flag                         false
% 2.56/1.02  --inst_sos_phase                        true
% 2.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel_side                     none
% 2.56/1.02  --inst_solver_per_active                1400
% 2.56/1.02  --inst_solver_calls_frac                1.
% 2.56/1.02  --inst_passive_queue_type               priority_queues
% 2.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.02  --inst_passive_queues_freq              [25;2]
% 2.56/1.02  --inst_dismatching                      true
% 2.56/1.02  --inst_eager_unprocessed_to_passive     true
% 2.56/1.02  --inst_prop_sim_given                   true
% 2.56/1.02  --inst_prop_sim_new                     false
% 2.56/1.02  --inst_subs_new                         false
% 2.56/1.02  --inst_eq_res_simp                      false
% 2.56/1.02  --inst_subs_given                       false
% 2.56/1.02  --inst_orphan_elimination               true
% 2.56/1.02  --inst_learning_loop_flag               true
% 2.56/1.02  --inst_learning_start                   3000
% 2.56/1.02  --inst_learning_factor                  2
% 2.56/1.02  --inst_start_prop_sim_after_learn       3
% 2.56/1.02  --inst_sel_renew                        solver
% 2.56/1.02  --inst_lit_activity_flag                true
% 2.56/1.02  --inst_restr_to_given                   false
% 2.56/1.02  --inst_activity_threshold               500
% 2.56/1.02  --inst_out_proof                        true
% 2.56/1.02  
% 2.56/1.02  ------ Resolution Options
% 2.56/1.02  
% 2.56/1.02  --resolution_flag                       false
% 2.56/1.02  --res_lit_sel                           adaptive
% 2.56/1.02  --res_lit_sel_side                      none
% 2.56/1.02  --res_ordering                          kbo
% 2.56/1.02  --res_to_prop_solver                    active
% 2.56/1.02  --res_prop_simpl_new                    false
% 2.56/1.02  --res_prop_simpl_given                  true
% 2.56/1.02  --res_passive_queue_type                priority_queues
% 2.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.02  --res_passive_queues_freq               [15;5]
% 2.56/1.02  --res_forward_subs                      full
% 2.56/1.02  --res_backward_subs                     full
% 2.56/1.02  --res_forward_subs_resolution           true
% 2.56/1.02  --res_backward_subs_resolution          true
% 2.56/1.02  --res_orphan_elimination                true
% 2.56/1.02  --res_time_limit                        2.
% 2.56/1.02  --res_out_proof                         true
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Options
% 2.56/1.02  
% 2.56/1.02  --superposition_flag                    true
% 2.56/1.02  --sup_passive_queue_type                priority_queues
% 2.56/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.02  --demod_completeness_check              fast
% 2.56/1.02  --demod_use_ground                      true
% 2.56/1.02  --sup_to_prop_solver                    passive
% 2.56/1.02  --sup_prop_simpl_new                    true
% 2.56/1.02  --sup_prop_simpl_given                  true
% 2.56/1.02  --sup_fun_splitting                     false
% 2.56/1.02  --sup_smt_interval                      50000
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Simplification Setup
% 2.56/1.02  
% 2.56/1.02  --sup_indices_passive                   []
% 2.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_full_bw                           [BwDemod]
% 2.56/1.02  --sup_immed_triv                        [TrivRules]
% 2.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_immed_bw_main                     []
% 2.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  
% 2.56/1.02  ------ Combination Options
% 2.56/1.02  
% 2.56/1.02  --comb_res_mult                         3
% 2.56/1.02  --comb_sup_mult                         2
% 2.56/1.02  --comb_inst_mult                        10
% 2.56/1.02  
% 2.56/1.02  ------ Debug Options
% 2.56/1.02  
% 2.56/1.02  --dbg_backtrace                         false
% 2.56/1.02  --dbg_dump_prop_clauses                 false
% 2.56/1.02  --dbg_dump_prop_clauses_file            -
% 2.56/1.02  --dbg_out_stat                          false
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  ------ Proving...
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  % SZS status Theorem for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  fof(f9,axiom,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f17,plain,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.56/1.02  
% 2.56/1.02  fof(f18,plain,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f17])).
% 2.56/1.02  
% 2.56/1.02  fof(f19,plain,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f18])).
% 2.56/1.02  
% 2.56/1.02  fof(f20,plain,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f19])).
% 2.56/1.02  
% 2.56/1.02  fof(f39,plain,(
% 2.56/1.02    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f20])).
% 2.56/1.02  
% 2.56/1.02  fof(f40,plain,(
% 2.56/1.02    ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f39])).
% 2.56/1.02  
% 2.56/1.02  fof(f67,plain,(
% 2.56/1.02    ( ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f40])).
% 2.56/1.02  
% 2.56/1.02  fof(f11,axiom,(
% 2.56/1.02    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f23,plain,(
% 2.56/1.02    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f11])).
% 2.56/1.02  
% 2.56/1.02  fof(f69,plain,(
% 2.56/1.02    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f23])).
% 2.56/1.02  
% 2.56/1.02  fof(f10,axiom,(
% 2.56/1.02    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f21,plain,(
% 2.56/1.02    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f10])).
% 2.56/1.02  
% 2.56/1.02  fof(f68,plain,(
% 2.56/1.02    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f21])).
% 2.56/1.02  
% 2.56/1.02  fof(f8,axiom,(
% 2.56/1.02    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f22,plain,(
% 2.56/1.02    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f8])).
% 2.56/1.02  
% 2.56/1.02  fof(f66,plain,(
% 2.56/1.02    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f22])).
% 2.56/1.02  
% 2.56/1.02  fof(f2,axiom,(
% 2.56/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f29,plain,(
% 2.56/1.02    ! [X0,X1] : ((l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.56/1.02    inference(ennf_transformation,[],[f2])).
% 2.56/1.02  
% 2.56/1.02  fof(f55,plain,(
% 2.56/1.02    ( ! [X0,X1] : (l1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f29])).
% 2.56/1.02  
% 2.56/1.02  fof(f6,axiom,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f35,plain,(
% 2.56/1.02    ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f6])).
% 2.56/1.02  
% 2.56/1.02  fof(f36,plain,(
% 2.56/1.02    ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f35])).
% 2.56/1.02  
% 2.56/1.02  fof(f64,plain,(
% 2.56/1.02    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f36])).
% 2.56/1.02  
% 2.56/1.02  fof(f1,axiom,(
% 2.56/1.02    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f27,plain,(
% 2.56/1.02    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 2.56/1.02    inference(ennf_transformation,[],[f1])).
% 2.56/1.02  
% 2.56/1.02  fof(f28,plain,(
% 2.56/1.02    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 2.56/1.02    inference(flattening,[],[f27])).
% 2.56/1.02  
% 2.56/1.02  fof(f53,plain,(
% 2.56/1.02    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f28])).
% 2.56/1.02  
% 2.56/1.02  fof(f54,plain,(
% 2.56/1.02    ( ! [X0,X1] : (v1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f29])).
% 2.56/1.02  
% 2.56/1.02  fof(f3,axiom,(
% 2.56/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f30,plain,(
% 2.56/1.02    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 2.56/1.02    inference(ennf_transformation,[],[f3])).
% 2.56/1.02  
% 2.56/1.02  fof(f56,plain,(
% 2.56/1.02    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f30])).
% 2.56/1.02  
% 2.56/1.02  fof(f15,conjecture,(
% 2.56/1.02    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f16,negated_conjecture,(
% 2.56/1.02    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 2.56/1.02    inference(negated_conjecture,[],[f15])).
% 2.56/1.02  
% 2.56/1.02  fof(f44,plain,(
% 2.56/1.02    ? [X0,X1] : (? [X2] : ((r3_orders_2(k3_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 2.56/1.02    inference(ennf_transformation,[],[f16])).
% 2.56/1.02  
% 2.56/1.02  fof(f48,plain,(
% 2.56/1.02    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 2.56/1.02    inference(nnf_transformation,[],[f44])).
% 2.56/1.02  
% 2.56/1.02  fof(f49,plain,(
% 2.56/1.02    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 2.56/1.02    inference(flattening,[],[f48])).
% 2.56/1.02  
% 2.56/1.02  fof(f51,plain,(
% 2.56/1.02    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) => ((~r1_tarski(X1,sK2) | ~r3_orders_2(k3_yellow_1(X0),X1,sK2)) & (r1_tarski(X1,sK2) | r3_orders_2(k3_yellow_1(X0),X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(X0))))) )),
% 2.56/1.02    introduced(choice_axiom,[])).
% 2.56/1.02  
% 2.56/1.02  fof(f50,plain,(
% 2.56/1.02    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 2.56/1.02    introduced(choice_axiom,[])).
% 2.56/1.02  
% 2.56/1.02  fof(f52,plain,(
% 2.56/1.02    ((~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 2.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f51,f50])).
% 2.56/1.02  
% 2.56/1.02  fof(f75,plain,(
% 2.56/1.02    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 2.56/1.02    inference(cnf_transformation,[],[f52])).
% 2.56/1.02  
% 2.56/1.02  fof(f14,axiom,(
% 2.56/1.02    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k3_yellow_1(X0)),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f74,plain,(
% 2.56/1.02    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = k3_yellow_1(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f14])).
% 2.56/1.02  
% 2.56/1.02  fof(f82,plain,(
% 2.56/1.02    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 2.56/1.02    inference(definition_unfolding,[],[f75,f74])).
% 2.56/1.02  
% 2.56/1.02  fof(f7,axiom,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f37,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f7])).
% 2.56/1.02  
% 2.56/1.02  fof(f38,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f37])).
% 2.56/1.02  
% 2.56/1.02  fof(f65,plain,(
% 2.56/1.02    ( ! [X0,X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f38])).
% 2.56/1.02  
% 2.56/1.02  fof(f76,plain,(
% 2.56/1.02    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 2.56/1.02    inference(cnf_transformation,[],[f52])).
% 2.56/1.02  
% 2.56/1.02  fof(f81,plain,(
% 2.56/1.02    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 2.56/1.02    inference(definition_unfolding,[],[f76,f74])).
% 2.56/1.02  
% 2.56/1.02  fof(f12,axiom,(
% 2.56/1.02    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f41,plain,(
% 2.56/1.02    ! [X0,X1] : (! [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 2.56/1.02    inference(ennf_transformation,[],[f12])).
% 2.56/1.02  
% 2.56/1.02  fof(f46,plain,(
% 2.56/1.02    ! [X0,X1] : (! [X2] : (((r1_lattices(k1_lattice3(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 2.56/1.02    inference(nnf_transformation,[],[f41])).
% 2.56/1.02  
% 2.56/1.02  fof(f71,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r1_lattices(k1_lattice3(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f4,axiom,(
% 2.56/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f24,plain,(
% 2.56/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f4])).
% 2.56/1.02  
% 2.56/1.02  fof(f25,plain,(
% 2.56/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f24])).
% 2.56/1.02  
% 2.56/1.02  fof(f26,plain,(
% 2.56/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f25])).
% 2.56/1.02  
% 2.56/1.02  fof(f31,plain,(
% 2.56/1.02    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.56/1.02    inference(ennf_transformation,[],[f26])).
% 2.56/1.02  
% 2.56/1.02  fof(f32,plain,(
% 2.56/1.02    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.56/1.02    inference(flattening,[],[f31])).
% 2.56/1.02  
% 2.56/1.02  fof(f61,plain,(
% 2.56/1.02    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f32])).
% 2.56/1.02  
% 2.56/1.02  fof(f5,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f33,plain,(
% 2.56/1.02    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f5])).
% 2.56/1.02  
% 2.56/1.02  fof(f34,plain,(
% 2.56/1.02    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f33])).
% 2.56/1.02  
% 2.56/1.02  fof(f45,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(nnf_transformation,[],[f34])).
% 2.56/1.02  
% 2.56/1.02  fof(f63,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f45])).
% 2.56/1.02  
% 2.56/1.02  fof(f59,plain,(
% 2.56/1.02    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f32])).
% 2.56/1.02  
% 2.56/1.02  fof(f60,plain,(
% 2.56/1.02    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f32])).
% 2.56/1.02  
% 2.56/1.02  fof(f13,axiom,(
% 2.56/1.02    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f42,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f13])).
% 2.56/1.02  
% 2.56/1.02  fof(f43,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f42])).
% 2.56/1.02  
% 2.56/1.02  fof(f47,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(nnf_transformation,[],[f43])).
% 2.56/1.02  
% 2.56/1.02  fof(f72,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f47])).
% 2.56/1.02  
% 2.56/1.02  fof(f73,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f47])).
% 2.56/1.02  
% 2.56/1.02  fof(f62,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f45])).
% 2.56/1.02  
% 2.56/1.02  fof(f70,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f77,plain,(
% 2.56/1.02    r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 2.56/1.02    inference(cnf_transformation,[],[f52])).
% 2.56/1.02  
% 2.56/1.02  fof(f80,plain,(
% 2.56/1.02    r1_tarski(sK1,sK2) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 2.56/1.02    inference(definition_unfolding,[],[f77,f74])).
% 2.56/1.02  
% 2.56/1.02  fof(f78,plain,(
% 2.56/1.02    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 2.56/1.02    inference(cnf_transformation,[],[f52])).
% 2.56/1.02  
% 2.56/1.02  fof(f79,plain,(
% 2.56/1.02    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 2.56/1.02    inference(definition_unfolding,[],[f78,f74])).
% 2.56/1.02  
% 2.56/1.02  cnf(c_14,plain,
% 2.56/1.02      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_16,plain,
% 2.56/1.02      ( v10_lattices(k1_lattice3(X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_713,plain,
% 2.56/1.02      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | k1_lattice3(X1) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_714,plain,
% 2.56/1.02      ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0)))))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_713]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_15,plain,
% 2.56/1.02      ( ~ v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_13,plain,
% 2.56/1.02      ( l3_lattices(k1_lattice3(X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_718,plain,
% 2.56/1.02      ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_714,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1857,plain,
% 2.56/1.02      ( m1_subset_1(k2_lattice3(k1_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X0)),u1_struct_0(k1_lattice3(X0))))) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.56/1.02      | l1_orders_2(g1_orders_2(X1,X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1865,plain,
% 2.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.56/1.02      | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2232,plain,
% 2.56/1.02      ( l1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) = iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1857,c_1865]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_11,plain,
% 2.56/1.02      ( ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0)
% 2.56/1.02      | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_728,plain,
% 2.56/1.02      ( ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) = k3_lattice3(X0)
% 2.56/1.02      | k1_lattice3(X1) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_729,plain,
% 2.56/1.02      ( ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0))
% 2.56/1.02      | g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) = k3_lattice3(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_728]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_733,plain,
% 2.56/1.02      ( g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0))) = k3_lattice3(k1_lattice3(X0)) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_729,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2233,plain,
% 2.56/1.02      ( l1_orders_2(k3_lattice3(k1_lattice3(X0))) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2232,c_733]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_0,plain,
% 2.56/1.02      ( ~ l1_orders_2(X0)
% 2.56/1.02      | ~ v1_orders_2(X0)
% 2.56/1.02      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
% 2.56/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1866,plain,
% 2.56/1.02      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
% 2.56/1.02      | l1_orders_2(X0) != iProver_top
% 2.56/1.02      | v1_orders_2(X0) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2389,plain,
% 2.56/1.02      ( g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) = k3_lattice3(k1_lattice3(X0))
% 2.56/1.02      | v1_orders_2(k3_lattice3(k1_lattice3(X0))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_2233,c_1866]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.56/1.02      | v1_orders_2(g1_orders_2(X1,X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1864,plain,
% 2.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.56/1.02      | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2224,plain,
% 2.56/1.02      ( v1_orders_2(g1_orders_2(u1_struct_0(k1_lattice3(X0)),k2_lattice3(k1_lattice3(X0)))) = iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1857,c_1864]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2225,plain,
% 2.56/1.02      ( v1_orders_2(k3_lattice3(k1_lattice3(X0))) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2224,c_733]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2468,plain,
% 2.56/1.02      ( g1_orders_2(u1_struct_0(k3_lattice3(k1_lattice3(X0))),u1_orders_2(k3_lattice3(k1_lattice3(X0)))) = k3_lattice3(k1_lattice3(X0)) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2389,c_2225]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.56/1.02      | X2 = X1
% 2.56/1.02      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1862,plain,
% 2.56/1.02      ( X0 = X1
% 2.56/1.02      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 2.56/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2290,plain,
% 2.56/1.02      ( g1_orders_2(X0,X1) != k3_lattice3(k1_lattice3(X2))
% 2.56/1.02      | u1_struct_0(k1_lattice3(X2)) = X0
% 2.56/1.02      | m1_subset_1(k2_lattice3(k1_lattice3(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_lattice3(X2)),u1_struct_0(k1_lattice3(X2))))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_733,c_1862]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2839,plain,
% 2.56/1.02      ( g1_orders_2(X0,X1) != k3_lattice3(k1_lattice3(X2))
% 2.56/1.02      | u1_struct_0(k1_lattice3(X2)) = X0 ),
% 2.56/1.02      inference(forward_subsumption_resolution,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2290,c_1857]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2842,plain,
% 2.56/1.02      ( k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(X1))
% 2.56/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = u1_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_2468,c_2839]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3161,plain,
% 2.56/1.02      ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) = u1_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(equality_resolution,[status(thm)],[c_2842]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_24,negated_conjecture,
% 2.56/1.02      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1858,plain,
% 2.56/1.02      ( m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3256,plain,
% 2.56/1.02      ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3161,c_1858]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_12,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/1.02      | ~ l3_lattices(X1)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | ~ v10_lattices(X1)
% 2.56/1.02      | k4_lattice3(X1,X0) = X0 ),
% 2.56/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_739,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/1.02      | ~ l3_lattices(X1)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | k4_lattice3(X1,X0) = X0
% 2.56/1.02      | k1_lattice3(X2) != X1 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_740,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X1))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X1))
% 2.56/1.02      | k4_lattice3(k1_lattice3(X1),X0) = X0 ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_739]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_752,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(X1)))
% 2.56/1.02      | k4_lattice3(k1_lattice3(X1),X0) = X0 ),
% 2.56/1.02      inference(forward_subsumption_resolution,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_740,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1856,plain,
% 2.56/1.02      ( k4_lattice3(k1_lattice3(X0),X1) = X1
% 2.56/1.02      | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3341,plain,
% 2.56/1.02      ( k4_lattice3(k1_lattice3(sK0),sK1) = sK1 ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3256,c_1856]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_23,negated_conjecture,
% 2.56/1.02      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1859,plain,
% 2.56/1.02      ( m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3255,plain,
% 2.56/1.02      ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3161,c_1859]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3282,plain,
% 2.56/1.02      ( k4_lattice3(k1_lattice3(sK0),sK2) = sK2 ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3255,c_1856]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_17,plain,
% 2.56/1.02      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ r1_tarski(X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_5,plain,
% 2.56/1.02      ( ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0)
% 2.56/1.02      | v9_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_9,plain,
% 2.56/1.02      ( ~ r1_lattices(X0,X1,X2)
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ v6_lattices(X0)
% 2.56/1.02      | ~ v8_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v9_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_477,plain,
% 2.56/1.02      ( ~ r1_lattices(X0,X1,X2)
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ v6_lattices(X0)
% 2.56/1.02      | ~ v8_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_7,plain,
% 2.56/1.02      ( v6_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_6,plain,
% 2.56/1.02      ( v8_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_481,plain,
% 2.56/1.02      ( ~ r1_lattices(X0,X1,X2)
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_477,c_7,c_6]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_617,plain,
% 2.56/1.02      ( ~ r1_lattices(X0,X1,X2)
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | k1_lattice3(X3) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_481,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_618,plain,
% 2.56/1.02      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_617]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_622,plain,
% 2.56/1.02      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_618,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_623,plain,
% 2.56/1.02      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_622]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_20,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_665,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | k1_lattice3(X3) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_666,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_665]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_670,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_666,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_671,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_670]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_870,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_623,c_671]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_984,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | ~ r1_tarski(X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_17,c_870]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1854,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) = iProver_top
% 2.56/1.02      | r1_tarski(X1,X2) != iProver_top
% 2.56/1.02      | m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) != iProver_top
% 2.56/1.02      | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3346,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) != iProver_top
% 2.56/1.02      | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3282,c_1854]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4120,plain,
% 2.56/1.02      ( m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) != iProver_top
% 2.56/1.02      | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_3346,c_3255]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4121,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) = iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) != iProver_top
% 2.56/1.02      | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_4120]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4130,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = iProver_top
% 2.56/1.02      | r1_tarski(sK1,sK2) != iProver_top
% 2.56/1.02      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3341,c_4121]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_19,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_689,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
% 2.56/1.02      | r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | k1_lattice3(X3) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_690,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_689]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_694,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_690,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_695,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_694]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_10,plain,
% 2.56/1.02      ( r1_lattices(X0,X1,X2)
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ v6_lattices(X0)
% 2.56/1.02      | ~ v8_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v9_lattices(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_445,plain,
% 2.56/1.02      ( r1_lattices(X0,X1,X2)
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ v6_lattices(X0)
% 2.56/1.02      | ~ v8_lattices(X0)
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_5,c_10]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_449,plain,
% 2.56/1.02      ( r1_lattices(X0,X1,X2)
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ v10_lattices(X0) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_445,c_7,c_6]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_641,plain,
% 2.56/1.02      ( r1_lattices(X0,X1,X2)
% 2.56/1.02      | ~ r3_lattices(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.02      | ~ l3_lattices(X0)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | k1_lattice3(X3) != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_449,c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_642,plain,
% 2.56/1.02      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ l3_lattices(k1_lattice3(X0))
% 2.56/1.02      | v2_struct_0(k1_lattice3(X0)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_641]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_646,plain,
% 2.56/1.02      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_642,c_15,c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_647,plain,
% 2.56/1.02      ( r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ r3_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_646]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_853,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_695,c_647]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_18,plain,
% 2.56/1.02      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
% 2.56/1.02      | r1_tarski(X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_967,plain,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2))
% 2.56/1.02      | r1_tarski(X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
% 2.56/1.02      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_853,c_18]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1855,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(X0)),k4_lattice3(k1_lattice3(X0),X1),k4_lattice3(k1_lattice3(X0),X2)) != iProver_top
% 2.56/1.02      | r1_tarski(X1,X2) = iProver_top
% 2.56/1.02      | m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) != iProver_top
% 2.56/1.02      | m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3345,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) = iProver_top
% 2.56/1.02      | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3282,c_1855]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3899,plain,
% 2.56/1.02      ( m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) = iProver_top
% 2.56/1.02      | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_3345,c_3255]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3900,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),k4_lattice3(k1_lattice3(sK0),X0),sK2) != iProver_top
% 2.56/1.02      | r1_tarski(X0,sK2) = iProver_top
% 2.56/1.02      | m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_3899]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3909,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != iProver_top
% 2.56/1.02      | r1_tarski(sK1,sK2) = iProver_top
% 2.56/1.02      | m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3341,c_3900]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_22,negated_conjecture,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 2.56/1.02      | r1_tarski(sK1,sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_27,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = iProver_top
% 2.56/1.02      | r1_tarski(sK1,sK2) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3979,plain,
% 2.56/1.02      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_3909,c_27,c_3256]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_21,negated_conjecture,
% 2.56/1.02      ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
% 2.56/1.02      | ~ r1_tarski(sK1,sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_28,plain,
% 2.56/1.02      ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) != iProver_top
% 2.56/1.02      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(contradiction,plain,
% 2.56/1.02      ( $false ),
% 2.56/1.02      inference(minisat,[status(thm)],[c_4130,c_3979,c_3256,c_28]) ).
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  ------                               Statistics
% 2.56/1.02  
% 2.56/1.02  ------ General
% 2.56/1.02  
% 2.56/1.02  abstr_ref_over_cycles:                  0
% 2.56/1.02  abstr_ref_under_cycles:                 0
% 2.56/1.02  gc_basic_clause_elim:                   0
% 2.56/1.02  forced_gc_time:                         0
% 2.56/1.02  parsing_time:                           0.009
% 2.56/1.02  unif_index_cands_time:                  0.
% 2.56/1.02  unif_index_add_time:                    0.
% 2.56/1.02  orderings_time:                         0.
% 2.56/1.02  out_proof_time:                         0.016
% 2.56/1.02  total_time:                             0.12
% 2.56/1.02  num_of_symbols:                         56
% 2.56/1.02  num_of_terms:                           3642
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing
% 2.56/1.02  
% 2.56/1.02  num_of_splits:                          0
% 2.56/1.02  num_of_split_atoms:                     0
% 2.56/1.02  num_of_reused_defs:                     0
% 2.56/1.02  num_eq_ax_congr_red:                    16
% 2.56/1.02  num_of_sem_filtered_clauses:            1
% 2.56/1.02  num_of_subtypes:                        0
% 2.56/1.02  monotx_restored_types:                  0
% 2.56/1.02  sat_num_of_epr_types:                   0
% 2.56/1.02  sat_num_of_non_cyclic_types:            0
% 2.56/1.02  sat_guarded_non_collapsed_types:        0
% 2.56/1.02  num_pure_diseq_elim:                    0
% 2.56/1.02  simp_replaced_by:                       0
% 2.56/1.02  res_preprocessed:                       97
% 2.56/1.02  prep_upred:                             0
% 2.56/1.02  prep_unflattend:                        23
% 2.56/1.02  smt_new_axioms:                         0
% 2.56/1.02  pred_elim_cands:                        5
% 2.56/1.02  pred_elim:                              8
% 2.56/1.02  pred_elim_cl:                           10
% 2.56/1.02  pred_elim_cycles:                       20
% 2.56/1.02  merged_defs:                            8
% 2.56/1.02  merged_defs_ncl:                        0
% 2.56/1.02  bin_hyper_res:                          8
% 2.56/1.02  prep_cycles:                            4
% 2.56/1.02  pred_elim_time:                         0.012
% 2.56/1.02  splitting_time:                         0.
% 2.56/1.02  sem_filter_time:                        0.
% 2.56/1.02  monotx_time:                            0.001
% 2.56/1.02  subtype_inf_time:                       0.
% 2.56/1.02  
% 2.56/1.02  ------ Problem properties
% 2.56/1.02  
% 2.56/1.02  clauses:                                14
% 2.56/1.02  conjectures:                            4
% 2.56/1.02  epr:                                    0
% 2.56/1.02  horn:                                   13
% 2.56/1.02  ground:                                 4
% 2.56/1.02  unary:                                  4
% 2.56/1.02  binary:                                 5
% 2.56/1.02  lits:                                   31
% 2.56/1.02  lits_eq:                                7
% 2.56/1.02  fd_pure:                                0
% 2.56/1.02  fd_pseudo:                              0
% 2.56/1.02  fd_cond:                                0
% 2.56/1.02  fd_pseudo_cond:                         2
% 2.56/1.02  ac_symbols:                             0
% 2.56/1.02  
% 2.56/1.02  ------ Propositional Solver
% 2.56/1.02  
% 2.56/1.02  prop_solver_calls:                      28
% 2.56/1.02  prop_fast_solver_calls:                 902
% 2.56/1.02  smt_solver_calls:                       0
% 2.56/1.02  smt_fast_solver_calls:                  0
% 2.56/1.02  prop_num_of_clauses:                    1175
% 2.56/1.02  prop_preprocess_simplified:             3941
% 2.56/1.02  prop_fo_subsumed:                       31
% 2.56/1.02  prop_solver_time:                       0.
% 2.56/1.02  smt_solver_time:                        0.
% 2.56/1.02  smt_fast_solver_time:                   0.
% 2.56/1.02  prop_fast_solver_time:                  0.
% 2.56/1.02  prop_unsat_core_time:                   0.
% 2.56/1.02  
% 2.56/1.02  ------ QBF
% 2.56/1.02  
% 2.56/1.02  qbf_q_res:                              0
% 2.56/1.02  qbf_num_tautologies:                    0
% 2.56/1.02  qbf_prep_cycles:                        0
% 2.56/1.02  
% 2.56/1.02  ------ BMC1
% 2.56/1.02  
% 2.56/1.02  bmc1_current_bound:                     -1
% 2.56/1.02  bmc1_last_solved_bound:                 -1
% 2.56/1.02  bmc1_unsat_core_size:                   -1
% 2.56/1.02  bmc1_unsat_core_parents_size:           -1
% 2.56/1.02  bmc1_merge_next_fun:                    0
% 2.56/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation
% 2.56/1.02  
% 2.56/1.02  inst_num_of_clauses:                    304
% 2.56/1.02  inst_num_in_passive:                    51
% 2.56/1.02  inst_num_in_active:                     211
% 2.56/1.02  inst_num_in_unprocessed:                42
% 2.56/1.02  inst_num_of_loops:                      220
% 2.56/1.02  inst_num_of_learning_restarts:          0
% 2.56/1.02  inst_num_moves_active_passive:          4
% 2.56/1.02  inst_lit_activity:                      0
% 2.56/1.02  inst_lit_activity_moves:                0
% 2.56/1.02  inst_num_tautologies:                   0
% 2.56/1.02  inst_num_prop_implied:                  0
% 2.56/1.02  inst_num_existing_simplified:           0
% 2.56/1.02  inst_num_eq_res_simplified:             0
% 2.56/1.02  inst_num_child_elim:                    0
% 2.56/1.02  inst_num_of_dismatching_blockings:      157
% 2.56/1.02  inst_num_of_non_proper_insts:           526
% 2.56/1.02  inst_num_of_duplicates:                 0
% 2.56/1.02  inst_inst_num_from_inst_to_res:         0
% 2.56/1.02  inst_dismatching_checking_time:         0.
% 2.56/1.02  
% 2.56/1.02  ------ Resolution
% 2.56/1.02  
% 2.56/1.02  res_num_of_clauses:                     0
% 2.56/1.02  res_num_in_passive:                     0
% 2.56/1.02  res_num_in_active:                      0
% 2.56/1.02  res_num_of_loops:                       101
% 2.56/1.02  res_forward_subset_subsumed:            62
% 2.56/1.02  res_backward_subset_subsumed:           2
% 2.56/1.02  res_forward_subsumed:                   0
% 2.56/1.02  res_backward_subsumed:                  0
% 2.56/1.02  res_forward_subsumption_resolution:     2
% 2.56/1.02  res_backward_subsumption_resolution:    0
% 2.56/1.02  res_clause_to_clause_subsumption:       119
% 2.56/1.02  res_orphan_elimination:                 0
% 2.56/1.02  res_tautology_del:                      90
% 2.56/1.02  res_num_eq_res_simplified:              0
% 2.56/1.02  res_num_sel_changes:                    0
% 2.56/1.02  res_moves_from_active_to_pass:          0
% 2.56/1.02  
% 2.56/1.02  ------ Superposition
% 2.56/1.02  
% 2.56/1.02  sup_time_total:                         0.
% 2.56/1.02  sup_time_generating:                    0.
% 2.56/1.02  sup_time_sim_full:                      0.
% 2.56/1.02  sup_time_sim_immed:                     0.
% 2.56/1.02  
% 2.56/1.02  sup_num_of_clauses:                     55
% 2.56/1.02  sup_num_in_active:                      34
% 2.56/1.02  sup_num_in_passive:                     21
% 2.56/1.02  sup_num_of_loops:                       42
% 2.56/1.02  sup_fw_superposition:                   34
% 2.56/1.02  sup_bw_superposition:                   18
% 2.56/1.02  sup_immediate_simplified:               3
% 2.56/1.02  sup_given_eliminated:                   0
% 2.56/1.02  comparisons_done:                       0
% 2.56/1.02  comparisons_avoided:                    0
% 2.56/1.02  
% 2.56/1.02  ------ Simplifications
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  sim_fw_subset_subsumed:                 1
% 2.56/1.02  sim_bw_subset_subsumed:                 6
% 2.56/1.02  sim_fw_subsumed:                        1
% 2.56/1.02  sim_bw_subsumed:                        0
% 2.56/1.02  sim_fw_subsumption_res:                 3
% 2.56/1.02  sim_bw_subsumption_res:                 0
% 2.56/1.02  sim_tautology_del:                      4
% 2.56/1.02  sim_eq_tautology_del:                   4
% 2.56/1.02  sim_eq_res_simp:                        0
% 2.56/1.02  sim_fw_demodulated:                     1
% 2.56/1.02  sim_bw_demodulated:                     7
% 2.56/1.02  sim_light_normalised:                   2
% 2.56/1.02  sim_joinable_taut:                      0
% 2.56/1.02  sim_joinable_simp:                      0
% 2.56/1.02  sim_ac_normalised:                      0
% 2.56/1.02  sim_smt_subsumption:                    0
% 2.56/1.02  
%------------------------------------------------------------------------------
