%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:02 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 189 expanded)
%              Number of clauses        :   45 (  47 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   22
%              Number of atoms          :  380 ( 806 expanded)
%              Number of equality atoms :   65 (  94 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,X1) )
     => ( v1_xboole_0(sK2)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(sK1,k3_yellow_1(X0))
        & v2_waybel_0(sK1,k3_yellow_1(X0))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).

fof(f61,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
    inference(definition_unfolding,[],[f61,f44])).

fof(f62,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
    inference(definition_unfolding,[],[f62,f44])).

fof(f64,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f60,f44])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))) ),
    inference(definition_unfolding,[],[f63,f44])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f45,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0] : l1_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f50,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0] : ~ v2_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f39,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( v1_yellow_0(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 = k5_lattices(k1_lattice3(X0))
      & v13_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v13_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f41,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f40,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0] : v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f52,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0] : v4_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f51,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] : v3_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f55,f38,f44])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f54,f44])).

cnf(c_24,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_23,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( l1_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_310,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_311,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0)
    | ~ v3_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ v4_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
    | ~ v1_yellow_0(k3_lattice3(k1_lattice3(X1)))
    | v2_struct_0(k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( ~ v2_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2,plain,
    ( l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( v1_yellow_0(k3_lattice3(X0))
    | ~ v13_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_293,plain,
    ( v1_yellow_0(k3_lattice3(X0))
    | ~ v13_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattice3(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_294,plain,
    ( v1_yellow_0(k3_lattice3(k1_lattice3(X0)))
    | ~ v13_lattices(k1_lattice3(X0))
    | ~ v10_lattices(k1_lattice3(X0))
    | v2_struct_0(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_6,plain,
    ( v13_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_298,plain,
    ( v1_yellow_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_6,c_4,c_3])).

cnf(c_12,plain,
    ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( v4_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( v3_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_337,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_311,c_1,c_15,c_298,c_12,c_13,c_14])).

cnf(c_423,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_337])).

cnf(c_424,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X0))),sK1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_600,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X0))),sK1)
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_424])).

cnf(c_630,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_600])).

cnf(c_662,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
    | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_630])).

cnf(c_692,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
    | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_662])).

cnf(c_714,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
    | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_692])).

cnf(c_724,plain,
    ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0_53))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0_53)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | k3_yellow_0(k3_lattice3(k1_lattice3(X0_53))) != sK2 ),
    inference(subtyping,[status(esa)],[c_714])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,negated_conjecture,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_456,plain,
    ( sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_457,plain,
    ( k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_727,plain,
    ( k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_17,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_728,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(X0_53))) = k1_zfmisc_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_16,plain,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_729,plain,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(X0_53))) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_769,plain,
    ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
    | u1_struct_0(k3_lattice3(k1_lattice3(sK0))) != k1_zfmisc_1(X0_53)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != k1_zfmisc_1(k1_zfmisc_1(X0_53))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_724,c_727,c_728,c_729])).

cnf(c_770,plain,
    ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
    | u1_struct_0(k3_lattice3(k1_lattice3(sK0))) != k1_zfmisc_1(X0_53)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != k1_zfmisc_1(k1_zfmisc_1(X0_53)) ),
    inference(equality_resolution_simp,[status(thm)],[c_769])).

cnf(c_771,plain,
    ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
    | k1_zfmisc_1(X0_53) != k1_zfmisc_1(sK0)
    | k1_zfmisc_1(k1_zfmisc_1(X0_53)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_770,c_728])).

cnf(c_794,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(equality_resolution,[status(thm)],[c_771])).

cnf(c_816,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_794])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:11:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.03/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.03/0.99  
% 1.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.03/0.99  
% 1.03/0.99  ------  iProver source info
% 1.03/0.99  
% 1.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.03/0.99  git: non_committed_changes: false
% 1.03/0.99  git: last_make_outside_of_git: false
% 1.03/0.99  
% 1.03/0.99  ------ 
% 1.03/0.99  
% 1.03/0.99  ------ Input Options
% 1.03/0.99  
% 1.03/0.99  --out_options                           all
% 1.03/0.99  --tptp_safe_out                         true
% 1.03/0.99  --problem_path                          ""
% 1.03/0.99  --include_path                          ""
% 1.03/0.99  --clausifier                            res/vclausify_rel
% 1.03/0.99  --clausifier_options                    --mode clausify
% 1.03/0.99  --stdin                                 false
% 1.03/0.99  --stats_out                             all
% 1.03/0.99  
% 1.03/0.99  ------ General Options
% 1.03/0.99  
% 1.03/0.99  --fof                                   false
% 1.03/0.99  --time_out_real                         305.
% 1.03/0.99  --time_out_virtual                      -1.
% 1.03/0.99  --symbol_type_check                     false
% 1.03/0.99  --clausify_out                          false
% 1.03/0.99  --sig_cnt_out                           false
% 1.03/0.99  --trig_cnt_out                          false
% 1.03/0.99  --trig_cnt_out_tolerance                1.
% 1.03/0.99  --trig_cnt_out_sk_spl                   false
% 1.03/0.99  --abstr_cl_out                          false
% 1.03/0.99  
% 1.03/0.99  ------ Global Options
% 1.03/0.99  
% 1.03/0.99  --schedule                              default
% 1.03/0.99  --add_important_lit                     false
% 1.03/0.99  --prop_solver_per_cl                    1000
% 1.03/0.99  --min_unsat_core                        false
% 1.03/0.99  --soft_assumptions                      false
% 1.03/0.99  --soft_lemma_size                       3
% 1.03/0.99  --prop_impl_unit_size                   0
% 1.03/0.99  --prop_impl_unit                        []
% 1.03/0.99  --share_sel_clauses                     true
% 1.03/0.99  --reset_solvers                         false
% 1.03/0.99  --bc_imp_inh                            [conj_cone]
% 1.03/0.99  --conj_cone_tolerance                   3.
% 1.03/0.99  --extra_neg_conj                        none
% 1.03/0.99  --large_theory_mode                     true
% 1.03/0.99  --prolific_symb_bound                   200
% 1.03/0.99  --lt_threshold                          2000
% 1.03/0.99  --clause_weak_htbl                      true
% 1.03/0.99  --gc_record_bc_elim                     false
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing Options
% 1.03/0.99  
% 1.03/0.99  --preprocessing_flag                    true
% 1.03/0.99  --time_out_prep_mult                    0.1
% 1.03/0.99  --splitting_mode                        input
% 1.03/0.99  --splitting_grd                         true
% 1.03/0.99  --splitting_cvd                         false
% 1.03/0.99  --splitting_cvd_svl                     false
% 1.03/0.99  --splitting_nvd                         32
% 1.03/0.99  --sub_typing                            true
% 1.03/0.99  --prep_gs_sim                           true
% 1.03/0.99  --prep_unflatten                        true
% 1.03/0.99  --prep_res_sim                          true
% 1.03/0.99  --prep_upred                            true
% 1.03/0.99  --prep_sem_filter                       exhaustive
% 1.03/0.99  --prep_sem_filter_out                   false
% 1.03/0.99  --pred_elim                             true
% 1.03/0.99  --res_sim_input                         true
% 1.03/0.99  --eq_ax_congr_red                       true
% 1.03/0.99  --pure_diseq_elim                       true
% 1.03/0.99  --brand_transform                       false
% 1.03/0.99  --non_eq_to_eq                          false
% 1.03/0.99  --prep_def_merge                        true
% 1.03/0.99  --prep_def_merge_prop_impl              false
% 1.03/0.99  --prep_def_merge_mbd                    true
% 1.03/0.99  --prep_def_merge_tr_red                 false
% 1.03/0.99  --prep_def_merge_tr_cl                  false
% 1.03/0.99  --smt_preprocessing                     true
% 1.03/0.99  --smt_ac_axioms                         fast
% 1.03/0.99  --preprocessed_out                      false
% 1.03/0.99  --preprocessed_stats                    false
% 1.03/0.99  
% 1.03/0.99  ------ Abstraction refinement Options
% 1.03/0.99  
% 1.03/0.99  --abstr_ref                             []
% 1.03/0.99  --abstr_ref_prep                        false
% 1.03/0.99  --abstr_ref_until_sat                   false
% 1.03/0.99  --abstr_ref_sig_restrict                funpre
% 1.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.03/0.99  --abstr_ref_under                       []
% 1.03/0.99  
% 1.03/0.99  ------ SAT Options
% 1.03/0.99  
% 1.03/0.99  --sat_mode                              false
% 1.03/0.99  --sat_fm_restart_options                ""
% 1.03/0.99  --sat_gr_def                            false
% 1.03/0.99  --sat_epr_types                         true
% 1.03/0.99  --sat_non_cyclic_types                  false
% 1.03/0.99  --sat_finite_models                     false
% 1.03/0.99  --sat_fm_lemmas                         false
% 1.03/0.99  --sat_fm_prep                           false
% 1.03/0.99  --sat_fm_uc_incr                        true
% 1.03/0.99  --sat_out_model                         small
% 1.03/0.99  --sat_out_clauses                       false
% 1.03/0.99  
% 1.03/0.99  ------ QBF Options
% 1.03/0.99  
% 1.03/0.99  --qbf_mode                              false
% 1.03/0.99  --qbf_elim_univ                         false
% 1.03/0.99  --qbf_dom_inst                          none
% 1.03/0.99  --qbf_dom_pre_inst                      false
% 1.03/0.99  --qbf_sk_in                             false
% 1.03/0.99  --qbf_pred_elim                         true
% 1.03/0.99  --qbf_split                             512
% 1.03/0.99  
% 1.03/0.99  ------ BMC1 Options
% 1.03/0.99  
% 1.03/0.99  --bmc1_incremental                      false
% 1.03/0.99  --bmc1_axioms                           reachable_all
% 1.03/0.99  --bmc1_min_bound                        0
% 1.03/0.99  --bmc1_max_bound                        -1
% 1.03/0.99  --bmc1_max_bound_default                -1
% 1.03/0.99  --bmc1_symbol_reachability              true
% 1.03/0.99  --bmc1_property_lemmas                  false
% 1.03/0.99  --bmc1_k_induction                      false
% 1.03/0.99  --bmc1_non_equiv_states                 false
% 1.03/0.99  --bmc1_deadlock                         false
% 1.03/0.99  --bmc1_ucm                              false
% 1.03/0.99  --bmc1_add_unsat_core                   none
% 1.03/0.99  --bmc1_unsat_core_children              false
% 1.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.03/0.99  --bmc1_out_stat                         full
% 1.03/0.99  --bmc1_ground_init                      false
% 1.03/0.99  --bmc1_pre_inst_next_state              false
% 1.03/0.99  --bmc1_pre_inst_state                   false
% 1.03/0.99  --bmc1_pre_inst_reach_state             false
% 1.03/0.99  --bmc1_out_unsat_core                   false
% 1.03/0.99  --bmc1_aig_witness_out                  false
% 1.03/0.99  --bmc1_verbose                          false
% 1.03/0.99  --bmc1_dump_clauses_tptp                false
% 1.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.03/0.99  --bmc1_dump_file                        -
% 1.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.03/0.99  --bmc1_ucm_extend_mode                  1
% 1.03/0.99  --bmc1_ucm_init_mode                    2
% 1.03/0.99  --bmc1_ucm_cone_mode                    none
% 1.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.03/0.99  --bmc1_ucm_relax_model                  4
% 1.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.03/0.99  --bmc1_ucm_layered_model                none
% 1.03/0.99  --bmc1_ucm_max_lemma_size               10
% 1.03/0.99  
% 1.03/0.99  ------ AIG Options
% 1.03/0.99  
% 1.03/0.99  --aig_mode                              false
% 1.03/0.99  
% 1.03/0.99  ------ Instantiation Options
% 1.03/0.99  
% 1.03/0.99  --instantiation_flag                    true
% 1.03/0.99  --inst_sos_flag                         false
% 1.03/0.99  --inst_sos_phase                        true
% 1.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.03/0.99  --inst_lit_sel_side                     num_symb
% 1.03/0.99  --inst_solver_per_active                1400
% 1.03/0.99  --inst_solver_calls_frac                1.
% 1.03/0.99  --inst_passive_queue_type               priority_queues
% 1.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.03/0.99  --inst_passive_queues_freq              [25;2]
% 1.03/0.99  --inst_dismatching                      true
% 1.03/0.99  --inst_eager_unprocessed_to_passive     true
% 1.03/0.99  --inst_prop_sim_given                   true
% 1.03/0.99  --inst_prop_sim_new                     false
% 1.03/0.99  --inst_subs_new                         false
% 1.03/0.99  --inst_eq_res_simp                      false
% 1.03/0.99  --inst_subs_given                       false
% 1.03/0.99  --inst_orphan_elimination               true
% 1.03/0.99  --inst_learning_loop_flag               true
% 1.03/0.99  --inst_learning_start                   3000
% 1.03/0.99  --inst_learning_factor                  2
% 1.03/0.99  --inst_start_prop_sim_after_learn       3
% 1.03/0.99  --inst_sel_renew                        solver
% 1.03/0.99  --inst_lit_activity_flag                true
% 1.03/0.99  --inst_restr_to_given                   false
% 1.03/0.99  --inst_activity_threshold               500
% 1.03/0.99  --inst_out_proof                        true
% 1.03/0.99  
% 1.03/0.99  ------ Resolution Options
% 1.03/0.99  
% 1.03/0.99  --resolution_flag                       true
% 1.03/0.99  --res_lit_sel                           adaptive
% 1.03/0.99  --res_lit_sel_side                      none
% 1.03/0.99  --res_ordering                          kbo
% 1.03/0.99  --res_to_prop_solver                    active
% 1.03/0.99  --res_prop_simpl_new                    false
% 1.03/0.99  --res_prop_simpl_given                  true
% 1.03/0.99  --res_passive_queue_type                priority_queues
% 1.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.03/0.99  --res_passive_queues_freq               [15;5]
% 1.03/0.99  --res_forward_subs                      full
% 1.03/0.99  --res_backward_subs                     full
% 1.03/0.99  --res_forward_subs_resolution           true
% 1.03/0.99  --res_backward_subs_resolution          true
% 1.03/0.99  --res_orphan_elimination                true
% 1.03/0.99  --res_time_limit                        2.
% 1.03/0.99  --res_out_proof                         true
% 1.03/0.99  
% 1.03/0.99  ------ Superposition Options
% 1.03/0.99  
% 1.03/0.99  --superposition_flag                    true
% 1.03/0.99  --sup_passive_queue_type                priority_queues
% 1.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.03/0.99  --demod_completeness_check              fast
% 1.03/0.99  --demod_use_ground                      true
% 1.03/0.99  --sup_to_prop_solver                    passive
% 1.03/0.99  --sup_prop_simpl_new                    true
% 1.03/0.99  --sup_prop_simpl_given                  true
% 1.03/0.99  --sup_fun_splitting                     false
% 1.03/0.99  --sup_smt_interval                      50000
% 1.03/0.99  
% 1.03/0.99  ------ Superposition Simplification Setup
% 1.03/0.99  
% 1.03/0.99  --sup_indices_passive                   []
% 1.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_full_bw                           [BwDemod]
% 1.03/0.99  --sup_immed_triv                        [TrivRules]
% 1.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_immed_bw_main                     []
% 1.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/0.99  
% 1.03/0.99  ------ Combination Options
% 1.03/0.99  
% 1.03/0.99  --comb_res_mult                         3
% 1.03/0.99  --comb_sup_mult                         2
% 1.03/0.99  --comb_inst_mult                        10
% 1.03/0.99  
% 1.03/0.99  ------ Debug Options
% 1.03/0.99  
% 1.03/0.99  --dbg_backtrace                         false
% 1.03/0.99  --dbg_dump_prop_clauses                 false
% 1.03/0.99  --dbg_dump_prop_clauses_file            -
% 1.03/0.99  --dbg_out_stat                          false
% 1.03/0.99  ------ Parsing...
% 1.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.03/0.99  ------ Proving...
% 1.03/0.99  ------ Problem Properties 
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  clauses                                 7
% 1.03/0.99  conjectures                             0
% 1.03/0.99  EPR                                     3
% 1.03/0.99  Horn                                    7
% 1.03/0.99  unary                                   6
% 1.03/0.99  binary                                  0
% 1.03/0.99  lits                                    10
% 1.03/0.99  lits eq                                 10
% 1.03/0.99  fd_pure                                 0
% 1.03/0.99  fd_pseudo                               0
% 1.03/0.99  fd_cond                                 0
% 1.03/0.99  fd_pseudo_cond                          0
% 1.03/0.99  AC symbols                              0
% 1.03/0.99  
% 1.03/0.99  ------ Schedule dynamic 5 is on 
% 1.03/0.99  
% 1.03/0.99  ------ no conjectures: strip conj schedule 
% 1.03/0.99  
% 1.03/0.99  ------ pure equality problem: resolution off 
% 1.03/0.99  
% 1.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  ------ 
% 1.03/0.99  Current options:
% 1.03/0.99  ------ 
% 1.03/0.99  
% 1.03/0.99  ------ Input Options
% 1.03/0.99  
% 1.03/0.99  --out_options                           all
% 1.03/0.99  --tptp_safe_out                         true
% 1.03/0.99  --problem_path                          ""
% 1.03/0.99  --include_path                          ""
% 1.03/0.99  --clausifier                            res/vclausify_rel
% 1.03/0.99  --clausifier_options                    --mode clausify
% 1.03/0.99  --stdin                                 false
% 1.03/0.99  --stats_out                             all
% 1.03/0.99  
% 1.03/0.99  ------ General Options
% 1.03/0.99  
% 1.03/0.99  --fof                                   false
% 1.03/0.99  --time_out_real                         305.
% 1.03/0.99  --time_out_virtual                      -1.
% 1.03/0.99  --symbol_type_check                     false
% 1.03/0.99  --clausify_out                          false
% 1.03/0.99  --sig_cnt_out                           false
% 1.03/0.99  --trig_cnt_out                          false
% 1.03/0.99  --trig_cnt_out_tolerance                1.
% 1.03/0.99  --trig_cnt_out_sk_spl                   false
% 1.03/0.99  --abstr_cl_out                          false
% 1.03/0.99  
% 1.03/0.99  ------ Global Options
% 1.03/0.99  
% 1.03/0.99  --schedule                              default
% 1.03/0.99  --add_important_lit                     false
% 1.03/0.99  --prop_solver_per_cl                    1000
% 1.03/0.99  --min_unsat_core                        false
% 1.03/0.99  --soft_assumptions                      false
% 1.03/0.99  --soft_lemma_size                       3
% 1.03/0.99  --prop_impl_unit_size                   0
% 1.03/0.99  --prop_impl_unit                        []
% 1.03/0.99  --share_sel_clauses                     true
% 1.03/0.99  --reset_solvers                         false
% 1.03/0.99  --bc_imp_inh                            [conj_cone]
% 1.03/0.99  --conj_cone_tolerance                   3.
% 1.03/0.99  --extra_neg_conj                        none
% 1.03/0.99  --large_theory_mode                     true
% 1.03/0.99  --prolific_symb_bound                   200
% 1.03/0.99  --lt_threshold                          2000
% 1.03/0.99  --clause_weak_htbl                      true
% 1.03/0.99  --gc_record_bc_elim                     false
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing Options
% 1.03/0.99  
% 1.03/0.99  --preprocessing_flag                    true
% 1.03/0.99  --time_out_prep_mult                    0.1
% 1.03/0.99  --splitting_mode                        input
% 1.03/0.99  --splitting_grd                         true
% 1.03/0.99  --splitting_cvd                         false
% 1.03/0.99  --splitting_cvd_svl                     false
% 1.03/0.99  --splitting_nvd                         32
% 1.03/0.99  --sub_typing                            true
% 1.03/0.99  --prep_gs_sim                           true
% 1.03/0.99  --prep_unflatten                        true
% 1.03/0.99  --prep_res_sim                          true
% 1.03/0.99  --prep_upred                            true
% 1.03/0.99  --prep_sem_filter                       exhaustive
% 1.03/0.99  --prep_sem_filter_out                   false
% 1.03/0.99  --pred_elim                             true
% 1.03/0.99  --res_sim_input                         true
% 1.03/0.99  --eq_ax_congr_red                       true
% 1.03/0.99  --pure_diseq_elim                       true
% 1.03/0.99  --brand_transform                       false
% 1.03/0.99  --non_eq_to_eq                          false
% 1.03/0.99  --prep_def_merge                        true
% 1.03/0.99  --prep_def_merge_prop_impl              false
% 1.03/0.99  --prep_def_merge_mbd                    true
% 1.03/0.99  --prep_def_merge_tr_red                 false
% 1.03/0.99  --prep_def_merge_tr_cl                  false
% 1.03/0.99  --smt_preprocessing                     true
% 1.03/0.99  --smt_ac_axioms                         fast
% 1.03/0.99  --preprocessed_out                      false
% 1.03/0.99  --preprocessed_stats                    false
% 1.03/0.99  
% 1.03/0.99  ------ Abstraction refinement Options
% 1.03/0.99  
% 1.03/0.99  --abstr_ref                             []
% 1.03/0.99  --abstr_ref_prep                        false
% 1.03/0.99  --abstr_ref_until_sat                   false
% 1.03/0.99  --abstr_ref_sig_restrict                funpre
% 1.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.03/0.99  --abstr_ref_under                       []
% 1.03/0.99  
% 1.03/0.99  ------ SAT Options
% 1.03/0.99  
% 1.03/0.99  --sat_mode                              false
% 1.03/0.99  --sat_fm_restart_options                ""
% 1.03/0.99  --sat_gr_def                            false
% 1.03/0.99  --sat_epr_types                         true
% 1.03/0.99  --sat_non_cyclic_types                  false
% 1.03/0.99  --sat_finite_models                     false
% 1.03/0.99  --sat_fm_lemmas                         false
% 1.03/0.99  --sat_fm_prep                           false
% 1.03/0.99  --sat_fm_uc_incr                        true
% 1.03/0.99  --sat_out_model                         small
% 1.03/0.99  --sat_out_clauses                       false
% 1.03/0.99  
% 1.03/0.99  ------ QBF Options
% 1.03/0.99  
% 1.03/0.99  --qbf_mode                              false
% 1.03/0.99  --qbf_elim_univ                         false
% 1.03/0.99  --qbf_dom_inst                          none
% 1.03/0.99  --qbf_dom_pre_inst                      false
% 1.03/0.99  --qbf_sk_in                             false
% 1.03/0.99  --qbf_pred_elim                         true
% 1.03/0.99  --qbf_split                             512
% 1.03/0.99  
% 1.03/0.99  ------ BMC1 Options
% 1.03/0.99  
% 1.03/0.99  --bmc1_incremental                      false
% 1.03/0.99  --bmc1_axioms                           reachable_all
% 1.03/0.99  --bmc1_min_bound                        0
% 1.03/0.99  --bmc1_max_bound                        -1
% 1.03/0.99  --bmc1_max_bound_default                -1
% 1.03/0.99  --bmc1_symbol_reachability              true
% 1.03/0.99  --bmc1_property_lemmas                  false
% 1.03/0.99  --bmc1_k_induction                      false
% 1.03/0.99  --bmc1_non_equiv_states                 false
% 1.03/0.99  --bmc1_deadlock                         false
% 1.03/0.99  --bmc1_ucm                              false
% 1.03/0.99  --bmc1_add_unsat_core                   none
% 1.03/0.99  --bmc1_unsat_core_children              false
% 1.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.03/0.99  --bmc1_out_stat                         full
% 1.03/0.99  --bmc1_ground_init                      false
% 1.03/0.99  --bmc1_pre_inst_next_state              false
% 1.03/0.99  --bmc1_pre_inst_state                   false
% 1.03/0.99  --bmc1_pre_inst_reach_state             false
% 1.03/0.99  --bmc1_out_unsat_core                   false
% 1.03/0.99  --bmc1_aig_witness_out                  false
% 1.03/0.99  --bmc1_verbose                          false
% 1.03/0.99  --bmc1_dump_clauses_tptp                false
% 1.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.03/0.99  --bmc1_dump_file                        -
% 1.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.03/0.99  --bmc1_ucm_extend_mode                  1
% 1.03/0.99  --bmc1_ucm_init_mode                    2
% 1.03/0.99  --bmc1_ucm_cone_mode                    none
% 1.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.03/0.99  --bmc1_ucm_relax_model                  4
% 1.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.03/0.99  --bmc1_ucm_layered_model                none
% 1.03/0.99  --bmc1_ucm_max_lemma_size               10
% 1.03/0.99  
% 1.03/0.99  ------ AIG Options
% 1.03/0.99  
% 1.03/0.99  --aig_mode                              false
% 1.03/0.99  
% 1.03/0.99  ------ Instantiation Options
% 1.03/0.99  
% 1.03/0.99  --instantiation_flag                    true
% 1.03/0.99  --inst_sos_flag                         false
% 1.03/0.99  --inst_sos_phase                        true
% 1.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.03/0.99  --inst_lit_sel_side                     none
% 1.03/0.99  --inst_solver_per_active                1400
% 1.03/0.99  --inst_solver_calls_frac                1.
% 1.03/0.99  --inst_passive_queue_type               priority_queues
% 1.03/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.03/0.99  --inst_passive_queues_freq              [25;2]
% 1.03/0.99  --inst_dismatching                      true
% 1.03/0.99  --inst_eager_unprocessed_to_passive     true
% 1.03/0.99  --inst_prop_sim_given                   true
% 1.03/0.99  --inst_prop_sim_new                     false
% 1.03/0.99  --inst_subs_new                         false
% 1.03/0.99  --inst_eq_res_simp                      false
% 1.03/0.99  --inst_subs_given                       false
% 1.03/0.99  --inst_orphan_elimination               true
% 1.03/0.99  --inst_learning_loop_flag               true
% 1.03/0.99  --inst_learning_start                   3000
% 1.03/0.99  --inst_learning_factor                  2
% 1.03/0.99  --inst_start_prop_sim_after_learn       3
% 1.03/0.99  --inst_sel_renew                        solver
% 1.03/0.99  --inst_lit_activity_flag                true
% 1.03/0.99  --inst_restr_to_given                   false
% 1.03/0.99  --inst_activity_threshold               500
% 1.03/0.99  --inst_out_proof                        true
% 1.03/0.99  
% 1.03/0.99  ------ Resolution Options
% 1.03/0.99  
% 1.03/0.99  --resolution_flag                       false
% 1.03/0.99  --res_lit_sel                           adaptive
% 1.03/0.99  --res_lit_sel_side                      none
% 1.03/0.99  --res_ordering                          kbo
% 1.03/0.99  --res_to_prop_solver                    active
% 1.03/0.99  --res_prop_simpl_new                    false
% 1.03/0.99  --res_prop_simpl_given                  true
% 1.03/0.99  --res_passive_queue_type                priority_queues
% 1.03/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.03/0.99  --res_passive_queues_freq               [15;5]
% 1.03/0.99  --res_forward_subs                      full
% 1.03/0.99  --res_backward_subs                     full
% 1.03/0.99  --res_forward_subs_resolution           true
% 1.03/0.99  --res_backward_subs_resolution          true
% 1.03/0.99  --res_orphan_elimination                true
% 1.03/0.99  --res_time_limit                        2.
% 1.03/0.99  --res_out_proof                         true
% 1.03/0.99  
% 1.03/0.99  ------ Superposition Options
% 1.03/0.99  
% 1.03/0.99  --superposition_flag                    true
% 1.03/0.99  --sup_passive_queue_type                priority_queues
% 1.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.03/0.99  --demod_completeness_check              fast
% 1.03/0.99  --demod_use_ground                      true
% 1.03/0.99  --sup_to_prop_solver                    passive
% 1.03/0.99  --sup_prop_simpl_new                    true
% 1.03/0.99  --sup_prop_simpl_given                  true
% 1.03/0.99  --sup_fun_splitting                     false
% 1.03/0.99  --sup_smt_interval                      50000
% 1.03/0.99  
% 1.03/0.99  ------ Superposition Simplification Setup
% 1.03/0.99  
% 1.03/0.99  --sup_indices_passive                   []
% 1.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_full_bw                           [BwDemod]
% 1.03/0.99  --sup_immed_triv                        [TrivRules]
% 1.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_immed_bw_main                     []
% 1.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.03/0.99  
% 1.03/0.99  ------ Combination Options
% 1.03/0.99  
% 1.03/0.99  --comb_res_mult                         3
% 1.03/0.99  --comb_sup_mult                         2
% 1.03/0.99  --comb_inst_mult                        10
% 1.03/0.99  
% 1.03/0.99  ------ Debug Options
% 1.03/0.99  
% 1.03/0.99  --dbg_backtrace                         false
% 1.03/0.99  --dbg_dump_prop_clauses                 false
% 1.03/0.99  --dbg_dump_prop_clauses_file            -
% 1.03/0.99  --dbg_out_stat                          false
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  ------ Proving...
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  % SZS status Theorem for theBenchmark.p
% 1.03/0.99  
% 1.03/0.99   Resolution empty clause
% 1.03/0.99  
% 1.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.03/0.99  
% 1.03/0.99  fof(f15,conjecture,(
% 1.03/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f16,negated_conjecture,(
% 1.03/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.03/0.99    inference(negated_conjecture,[],[f15])).
% 1.03/0.99  
% 1.03/0.99  fof(f29,plain,(
% 1.03/0.99    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.03/0.99    inference(ennf_transformation,[],[f16])).
% 1.03/0.99  
% 1.03/0.99  fof(f30,plain,(
% 1.03/0.99    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.03/0.99    inference(flattening,[],[f29])).
% 1.03/0.99  
% 1.03/0.99  fof(f34,plain,(
% 1.03/0.99    ( ! [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) => (v1_xboole_0(sK2) & r2_hidden(sK2,X1))) )),
% 1.03/0.99    introduced(choice_axiom,[])).
% 1.03/0.99  
% 1.03/0.99  fof(f33,plain,(
% 1.03/0.99    ( ! [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(sK1,k3_yellow_1(X0)) & v2_waybel_0(sK1,k3_yellow_1(X0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(sK1))) )),
% 1.03/0.99    introduced(choice_axiom,[])).
% 1.03/0.99  
% 1.03/0.99  fof(f32,plain,(
% 1.03/0.99    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(X1,k3_yellow_1(sK0)) & v2_waybel_0(X1,k3_yellow_1(sK0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.03/0.99    introduced(choice_axiom,[])).
% 1.03/0.99  
% 1.03/0.99  fof(f35,plain,(
% 1.03/0.99    ((v1_xboole_0(sK2) & r2_hidden(sK2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(sK1,k3_yellow_1(sK0)) & v2_waybel_0(sK1,k3_yellow_1(sK0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).
% 1.03/0.99  
% 1.03/0.99  fof(f61,plain,(
% 1.03/0.99    v2_waybel_0(sK1,k3_yellow_1(sK0))),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f8,axiom,(
% 1.03/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f44,plain,(
% 1.03/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f8])).
% 1.03/0.99  
% 1.03/0.99  fof(f75,plain,(
% 1.03/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0)))),
% 1.03/0.99    inference(definition_unfolding,[],[f61,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f62,plain,(
% 1.03/0.99    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f74,plain,(
% 1.03/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0)))),
% 1.03/0.99    inference(definition_unfolding,[],[f62,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f64,plain,(
% 1.03/0.99    r2_hidden(sK2,sK1)),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f60,plain,(
% 1.03/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f76,plain,(
% 1.03/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 1.03/0.99    inference(definition_unfolding,[],[f60,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f63,plain,(
% 1.03/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f73,plain,(
% 1.03/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))))),
% 1.03/0.99    inference(definition_unfolding,[],[f63,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f9,axiom,(
% 1.03/0.99    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f19,plain,(
% 1.03/0.99    ! [X0] : l1_orders_2(k3_yellow_1(X0))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.03/0.99  
% 1.03/0.99  fof(f45,plain,(
% 1.03/0.99    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f19])).
% 1.03/0.99  
% 1.03/0.99  fof(f66,plain,(
% 1.03/0.99    ( ! [X0] : (l1_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f45,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f14,axiom,(
% 1.03/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f27,plain,(
% 1.03/0.99    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.03/0.99    inference(ennf_transformation,[],[f14])).
% 1.03/0.99  
% 1.03/0.99  fof(f28,plain,(
% 1.03/0.99    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.03/0.99    inference(flattening,[],[f27])).
% 1.03/0.99  
% 1.03/0.99  fof(f31,plain,(
% 1.03/0.99    ! [X0] : (! [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k3_yellow_0(X0),X1)) & (~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.03/0.99    inference(nnf_transformation,[],[f28])).
% 1.03/0.99  
% 1.03/0.99  fof(f56,plain,(
% 1.03/0.99    ( ! [X0,X1] : (~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.03/0.99    inference(cnf_transformation,[],[f31])).
% 1.03/0.99  
% 1.03/0.99  fof(f2,axiom,(
% 1.03/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f24,plain,(
% 1.03/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.03/0.99    inference(ennf_transformation,[],[f2])).
% 1.03/0.99  
% 1.03/0.99  fof(f37,plain,(
% 1.03/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.03/0.99    inference(cnf_transformation,[],[f24])).
% 1.03/0.99  
% 1.03/0.99  fof(f11,axiom,(
% 1.03/0.99    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f18,plain,(
% 1.03/0.99    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f11])).
% 1.03/0.99  
% 1.03/0.99  fof(f50,plain,(
% 1.03/0.99    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f18])).
% 1.03/0.99  
% 1.03/0.99  fof(f70,plain,(
% 1.03/0.99    ( ! [X0] : (~v2_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f50,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f4,axiom,(
% 1.03/0.99    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f21,plain,(
% 1.03/0.99    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f4])).
% 1.03/0.99  
% 1.03/0.99  fof(f39,plain,(
% 1.03/0.99    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f21])).
% 1.03/0.99  
% 1.03/0.99  fof(f10,axiom,(
% 1.03/0.99    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f17,plain,(
% 1.03/0.99    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.03/0.99  
% 1.03/0.99  fof(f25,plain,(
% 1.03/0.99    ! [X0] : ((v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.03/0.99    inference(ennf_transformation,[],[f17])).
% 1.03/0.99  
% 1.03/0.99  fof(f26,plain,(
% 1.03/0.99    ! [X0] : ((v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.03/0.99    inference(flattening,[],[f25])).
% 1.03/0.99  
% 1.03/0.99  fof(f49,plain,(
% 1.03/0.99    ( ! [X0] : (v1_yellow_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.03/0.99    inference(cnf_transformation,[],[f26])).
% 1.03/0.99  
% 1.03/0.99  fof(f7,axiom,(
% 1.03/0.99    ! [X0] : (k1_xboole_0 = k5_lattices(k1_lattice3(X0)) & v13_lattices(k1_lattice3(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f42,plain,(
% 1.03/0.99    ( ! [X0] : (v13_lattices(k1_lattice3(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f7])).
% 1.03/0.99  
% 1.03/0.99  fof(f6,axiom,(
% 1.03/0.99    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f20,plain,(
% 1.03/0.99    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.03/0.99  
% 1.03/0.99  fof(f41,plain,(
% 1.03/0.99    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f20])).
% 1.03/0.99  
% 1.03/0.99  fof(f5,axiom,(
% 1.03/0.99    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f22,plain,(
% 1.03/0.99    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 1.03/0.99    inference(pure_predicate_removal,[],[f5])).
% 1.03/0.99  
% 1.03/0.99  fof(f40,plain,(
% 1.03/0.99    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f22])).
% 1.03/0.99  
% 1.03/0.99  fof(f53,plain,(
% 1.03/0.99    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f18])).
% 1.03/0.99  
% 1.03/0.99  fof(f67,plain,(
% 1.03/0.99    ( ! [X0] : (v5_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f53,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f52,plain,(
% 1.03/0.99    ( ! [X0] : (v4_orders_2(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f18])).
% 1.03/0.99  
% 1.03/0.99  fof(f68,plain,(
% 1.03/0.99    ( ! [X0] : (v4_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f52,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f51,plain,(
% 1.03/0.99    ( ! [X0] : (v3_orders_2(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f18])).
% 1.03/0.99  
% 1.03/0.99  fof(f69,plain,(
% 1.03/0.99    ( ! [X0] : (v3_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f51,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f1,axiom,(
% 1.03/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f23,plain,(
% 1.03/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.03/0.99    inference(ennf_transformation,[],[f1])).
% 1.03/0.99  
% 1.03/0.99  fof(f36,plain,(
% 1.03/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.03/0.99    inference(cnf_transformation,[],[f23])).
% 1.03/0.99  
% 1.03/0.99  fof(f65,plain,(
% 1.03/0.99    v1_xboole_0(sK2)),
% 1.03/0.99    inference(cnf_transformation,[],[f35])).
% 1.03/0.99  
% 1.03/0.99  fof(f13,axiom,(
% 1.03/0.99    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f55,plain,(
% 1.03/0.99    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f13])).
% 1.03/0.99  
% 1.03/0.99  fof(f3,axiom,(
% 1.03/0.99    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0)),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f38,plain,(
% 1.03/0.99    ( ! [X0] : (k9_setfam_1(X0) = k1_zfmisc_1(X0)) )),
% 1.03/0.99    inference(cnf_transformation,[],[f3])).
% 1.03/0.99  
% 1.03/0.99  fof(f72,plain,(
% 1.03/0.99    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f55,f38,f44])).
% 1.03/0.99  
% 1.03/0.99  fof(f12,axiom,(
% 1.03/0.99    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 1.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.03/0.99  
% 1.03/0.99  fof(f54,plain,(
% 1.03/0.99    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))) )),
% 1.03/0.99    inference(cnf_transformation,[],[f12])).
% 1.03/0.99  
% 1.03/0.99  fof(f71,plain,(
% 1.03/0.99    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_lattice3(k1_lattice3(X0)))) )),
% 1.03/0.99    inference(definition_unfolding,[],[f54,f44])).
% 1.03/0.99  
% 1.03/0.99  cnf(c_24,negated_conjecture,
% 1.03/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_23,negated_conjecture,
% 1.03/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(sK0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_21,negated_conjecture,
% 1.03/0.99      ( r2_hidden(sK2,sK1) ),
% 1.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_25,negated_conjecture,
% 1.03/0.99      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_22,negated_conjecture,
% 1.03/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_7,plain,
% 1.03/0.99      ( l1_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_19,plain,
% 1.03/0.99      ( ~ v2_waybel_0(X0,X1)
% 1.03/0.99      | ~ v13_waybel_0(X0,X1)
% 1.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.03/0.99      | ~ v1_subset_1(X0,u1_struct_0(X1))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(X1),X0)
% 1.03/0.99      | ~ v3_orders_2(X1)
% 1.03/0.99      | ~ v4_orders_2(X1)
% 1.03/0.99      | ~ v5_orders_2(X1)
% 1.03/0.99      | ~ v1_yellow_0(X1)
% 1.03/0.99      | ~ l1_orders_2(X1)
% 1.03/0.99      | v2_struct_0(X1)
% 1.03/0.99      | v1_xboole_0(X0) ),
% 1.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_310,plain,
% 1.03/0.99      ( ~ v2_waybel_0(X0,X1)
% 1.03/0.99      | ~ v13_waybel_0(X0,X1)
% 1.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.03/0.99      | ~ v1_subset_1(X0,u1_struct_0(X1))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(X1),X0)
% 1.03/0.99      | ~ v3_orders_2(X1)
% 1.03/0.99      | ~ v4_orders_2(X1)
% 1.03/0.99      | ~ v5_orders_2(X1)
% 1.03/0.99      | ~ v1_yellow_0(X1)
% 1.03/0.99      | v2_struct_0(X1)
% 1.03/0.99      | v1_xboole_0(X0)
% 1.03/0.99      | k3_lattice3(k1_lattice3(X2)) != X1 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_311,plain,
% 1.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.03/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0)
% 1.03/0.99      | ~ v3_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v4_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v1_yellow_0(k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | v2_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | v1_xboole_0(X0) ),
% 1.03/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_1,plain,
% 1.03/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.03/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_15,plain,
% 1.03/0.99      ( ~ v2_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_2,plain,
% 1.03/0.99      ( l3_lattices(k1_lattice3(X0)) ),
% 1.03/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_8,plain,
% 1.03/0.99      ( v1_yellow_0(k3_lattice3(X0))
% 1.03/0.99      | ~ v13_lattices(X0)
% 1.03/0.99      | ~ v10_lattices(X0)
% 1.03/0.99      | v2_struct_0(X0)
% 1.03/0.99      | ~ l3_lattices(X0) ),
% 1.03/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_293,plain,
% 1.03/0.99      ( v1_yellow_0(k3_lattice3(X0))
% 1.03/0.99      | ~ v13_lattices(X0)
% 1.03/0.99      | ~ v10_lattices(X0)
% 1.03/0.99      | v2_struct_0(X0)
% 1.03/0.99      | k1_lattice3(X1) != X0 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_294,plain,
% 1.03/0.99      ( v1_yellow_0(k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ v13_lattices(k1_lattice3(X0))
% 1.03/0.99      | ~ v10_lattices(k1_lattice3(X0))
% 1.03/0.99      | v2_struct_0(k1_lattice3(X0)) ),
% 1.03/0.99      inference(unflattening,[status(thm)],[c_293]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_6,plain,
% 1.03/0.99      ( v13_lattices(k1_lattice3(X0)) ),
% 1.03/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_4,plain,
% 1.03/0.99      ( v10_lattices(k1_lattice3(X0)) ),
% 1.03/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_3,plain,
% 1.03/0.99      ( ~ v2_struct_0(k1_lattice3(X0)) ),
% 1.03/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_298,plain,
% 1.03/0.99      ( v1_yellow_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(global_propositional_subsumption,
% 1.03/0.99                [status(thm)],
% 1.03/0.99                [c_294,c_6,c_4,c_3]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_12,plain,
% 1.03/0.99      ( v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_13,plain,
% 1.03/0.99      ( v4_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_14,plain,
% 1.03/0.99      ( v3_orders_2(k3_lattice3(k1_lattice3(X0))) ),
% 1.03/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_337,plain,
% 1.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.03/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0) ),
% 1.03/0.99      inference(forward_subsumption_resolution,
% 1.03/0.99                [status(thm)],
% 1.03/0.99                [c_311,c_1,c_15,c_298,c_12,c_13,c_14]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_423,plain,
% 1.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.03/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X1))),X0)
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | sK1 != X0 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_337]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_424,plain,
% 1.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X0))),sK1)
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
% 1.03/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_600,plain,
% 1.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ r2_hidden(k3_yellow_0(k3_lattice3(k1_lattice3(X0))),sK1)
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | sK1 != sK1 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_424]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_630,plain,
% 1.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
% 1.03/0.99      | sK1 != sK1 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_600]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_662,plain,
% 1.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
% 1.03/0.99      | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | sK1 != sK1 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_630]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_692,plain,
% 1.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
% 1.03/0.99      | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | sK1 != sK1 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_662]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_714,plain,
% 1.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | k3_yellow_0(k3_lattice3(k1_lattice3(X0))) != sK2
% 1.03/0.99      | k3_lattice3(k1_lattice3(X0)) != k3_lattice3(k1_lattice3(sK0)) ),
% 1.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_692]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_724,plain,
% 1.03/0.99      ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0_53))) != u1_struct_0(k3_lattice3(k1_lattice3(sK0)))
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0_53)))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
% 1.03/0.99      | k3_yellow_0(k3_lattice3(k1_lattice3(X0_53))) != sK2 ),
% 1.03/0.99      inference(subtyping,[status(esa)],[c_714]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_0,plain,
% 1.03/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.03/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_20,negated_conjecture,
% 1.03/0.99      ( v1_xboole_0(sK2) ),
% 1.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_456,plain,
% 1.03/0.99      ( sK2 != X0 | k1_xboole_0 = X0 ),
% 1.03/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_457,plain,
% 1.03/0.99      ( k1_xboole_0 = sK2 ),
% 1.03/0.99      inference(unflattening,[status(thm)],[c_456]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_727,plain,
% 1.03/0.99      ( k1_xboole_0 = sK2 ),
% 1.03/0.99      inference(subtyping,[status(esa)],[c_457]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_17,plain,
% 1.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(X0))) = k1_zfmisc_1(X0) ),
% 1.03/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_728,plain,
% 1.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(X0_53))) = k1_zfmisc_1(X0_53) ),
% 1.03/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_16,plain,
% 1.03/0.99      ( k3_yellow_0(k3_lattice3(k1_lattice3(X0))) = k1_xboole_0 ),
% 1.03/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_729,plain,
% 1.03/0.99      ( k3_yellow_0(k3_lattice3(k1_lattice3(X0_53))) = k1_xboole_0 ),
% 1.03/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_769,plain,
% 1.03/0.99      ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(sK0))) != k1_zfmisc_1(X0_53)
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != k1_zfmisc_1(k1_zfmisc_1(X0_53))
% 1.03/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.03/0.99      inference(light_normalisation,[status(thm)],[c_724,c_727,c_728,c_729]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_770,plain,
% 1.03/0.99      ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(sK0))) != k1_zfmisc_1(X0_53)
% 1.03/0.99      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) != k1_zfmisc_1(k1_zfmisc_1(X0_53)) ),
% 1.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_769]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_771,plain,
% 1.03/0.99      ( k3_lattice3(k1_lattice3(X0_53)) != k3_lattice3(k1_lattice3(sK0))
% 1.03/0.99      | k1_zfmisc_1(X0_53) != k1_zfmisc_1(sK0)
% 1.03/0.99      | k1_zfmisc_1(k1_zfmisc_1(X0_53)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 1.03/0.99      inference(demodulation,[status(thm)],[c_770,c_728]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_794,plain,
% 1.03/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 1.03/0.99      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 1.03/0.99      inference(equality_resolution,[status(thm)],[c_771]) ).
% 1.03/0.99  
% 1.03/0.99  cnf(c_816,plain,
% 1.03/0.99      ( $false ),
% 1.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_794]) ).
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.03/0.99  
% 1.03/0.99  ------                               Statistics
% 1.03/0.99  
% 1.03/0.99  ------ General
% 1.03/0.99  
% 1.03/0.99  abstr_ref_over_cycles:                  0
% 1.03/0.99  abstr_ref_under_cycles:                 0
% 1.03/0.99  gc_basic_clause_elim:                   0
% 1.03/0.99  forced_gc_time:                         0
% 1.03/0.99  parsing_time:                           0.012
% 1.03/0.99  unif_index_cands_time:                  0.
% 1.03/0.99  unif_index_add_time:                    0.
% 1.03/0.99  orderings_time:                         0.
% 1.03/0.99  out_proof_time:                         0.017
% 1.03/0.99  total_time:                             0.071
% 1.03/0.99  num_of_symbols:                         56
% 1.03/0.99  num_of_terms:                           972
% 1.03/0.99  
% 1.03/0.99  ------ Preprocessing
% 1.03/0.99  
% 1.03/0.99  num_of_splits:                          0
% 1.03/0.99  num_of_split_atoms:                     0
% 1.03/0.99  num_of_reused_defs:                     0
% 1.03/0.99  num_eq_ax_congr_red:                    0
% 1.03/0.99  num_of_sem_filtered_clauses:            0
% 1.03/0.99  num_of_subtypes:                        3
% 1.03/0.99  monotx_restored_types:                  0
% 1.03/0.99  sat_num_of_epr_types:                   0
% 1.03/0.99  sat_num_of_non_cyclic_types:            0
% 1.03/0.99  sat_guarded_non_collapsed_types:        0
% 1.03/0.99  num_pure_diseq_elim:                    0
% 1.03/0.99  simp_replaced_by:                       0
% 1.03/0.99  res_preprocessed:                       53
% 1.03/0.99  prep_upred:                             0
% 1.03/0.99  prep_unflattend:                        11
% 1.03/0.99  smt_new_axioms:                         0
% 1.03/0.99  pred_elim_cands:                        0
% 1.03/0.99  pred_elim:                              15
% 1.03/0.99  pred_elim_cl:                           21
% 1.03/0.99  pred_elim_cycles:                       18
% 1.03/0.99  merged_defs:                            0
% 1.03/0.99  merged_defs_ncl:                        0
% 1.03/0.99  bin_hyper_res:                          0
% 1.03/0.99  prep_cycles:                            3
% 1.03/0.99  pred_elim_time:                         0.011
% 1.03/0.99  splitting_time:                         0.
% 1.03/0.99  sem_filter_time:                        0.
% 1.03/0.99  monotx_time:                            0.
% 1.03/0.99  subtype_inf_time:                       0.
% 1.03/0.99  
% 1.03/0.99  ------ Problem properties
% 1.03/0.99  
% 1.03/0.99  clauses:                                7
% 1.03/0.99  conjectures:                            0
% 1.03/0.99  epr:                                    3
% 1.03/0.99  horn:                                   7
% 1.03/0.99  ground:                                 3
% 1.03/0.99  unary:                                  6
% 1.03/0.99  binary:                                 0
% 1.03/0.99  lits:                                   10
% 1.03/0.99  lits_eq:                                10
% 1.03/0.99  fd_pure:                                0
% 1.03/0.99  fd_pseudo:                              0
% 1.03/0.99  fd_cond:                                0
% 1.03/0.99  fd_pseudo_cond:                         0
% 1.03/0.99  ac_symbols:                             0
% 1.03/0.99  
% 1.03/0.99  ------ Propositional Solver
% 1.03/0.99  
% 1.03/0.99  prop_solver_calls:                      21
% 1.03/0.99  prop_fast_solver_calls:                 318
% 1.03/0.99  smt_solver_calls:                       0
% 1.03/0.99  smt_fast_solver_calls:                  0
% 1.03/0.99  prop_num_of_clauses:                    213
% 1.03/0.99  prop_preprocess_simplified:             1149
% 1.03/0.99  prop_fo_subsumed:                       4
% 1.03/0.99  prop_solver_time:                       0.
% 1.03/0.99  smt_solver_time:                        0.
% 1.03/0.99  smt_fast_solver_time:                   0.
% 1.03/0.99  prop_fast_solver_time:                  0.
% 1.03/0.99  prop_unsat_core_time:                   0.
% 1.03/0.99  
% 1.03/0.99  ------ QBF
% 1.03/0.99  
% 1.03/0.99  qbf_q_res:                              0
% 1.03/0.99  qbf_num_tautologies:                    0
% 1.03/0.99  qbf_prep_cycles:                        0
% 1.03/0.99  
% 1.03/0.99  ------ BMC1
% 1.03/0.99  
% 1.03/0.99  bmc1_current_bound:                     -1
% 1.03/0.99  bmc1_last_solved_bound:                 -1
% 1.03/0.99  bmc1_unsat_core_size:                   -1
% 1.03/0.99  bmc1_unsat_core_parents_size:           -1
% 1.03/0.99  bmc1_merge_next_fun:                    0
% 1.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.03/0.99  
% 1.03/0.99  ------ Instantiation
% 1.03/0.99  
% 1.03/0.99  inst_num_of_clauses:                    29
% 1.03/0.99  inst_num_in_passive:                    1
% 1.03/0.99  inst_num_in_active:                     27
% 1.03/0.99  inst_num_in_unprocessed:                1
% 1.03/0.99  inst_num_of_loops:                      30
% 1.03/0.99  inst_num_of_learning_restarts:          0
% 1.03/0.99  inst_num_moves_active_passive:          0
% 1.03/0.99  inst_lit_activity:                      0
% 1.03/0.99  inst_lit_activity_moves:                0
% 1.03/0.99  inst_num_tautologies:                   0
% 1.03/0.99  inst_num_prop_implied:                  0
% 1.03/0.99  inst_num_existing_simplified:           0
% 1.03/0.99  inst_num_eq_res_simplified:             0
% 1.03/0.99  inst_num_child_elim:                    0
% 1.03/0.99  inst_num_of_dismatching_blockings:      1
% 1.03/0.99  inst_num_of_non_proper_insts:           14
% 1.03/0.99  inst_num_of_duplicates:                 0
% 1.03/0.99  inst_inst_num_from_inst_to_res:         0
% 1.03/0.99  inst_dismatching_checking_time:         0.
% 1.03/0.99  
% 1.03/0.99  ------ Resolution
% 1.03/0.99  
% 1.03/0.99  res_num_of_clauses:                     0
% 1.03/0.99  res_num_in_passive:                     0
% 1.03/0.99  res_num_in_active:                      0
% 1.03/0.99  res_num_of_loops:                       56
% 1.03/0.99  res_forward_subset_subsumed:            8
% 1.03/0.99  res_backward_subset_subsumed:           0
% 1.03/0.99  res_forward_subsumed:                   0
% 1.03/0.99  res_backward_subsumed:                  0
% 1.03/0.99  res_forward_subsumption_resolution:     11
% 1.03/0.99  res_backward_subsumption_resolution:    0
% 1.03/0.99  res_clause_to_clause_subsumption:       38
% 1.03/0.99  res_orphan_elimination:                 0
% 1.03/0.99  res_tautology_del:                      3
% 1.03/0.99  res_num_eq_res_simplified:              1
% 1.03/0.99  res_num_sel_changes:                    0
% 1.03/0.99  res_moves_from_active_to_pass:          0
% 1.03/0.99  
% 1.03/0.99  ------ Superposition
% 1.03/0.99  
% 1.03/0.99  sup_time_total:                         0.
% 1.03/0.99  sup_time_generating:                    0.
% 1.03/0.99  sup_time_sim_full:                      0.
% 1.03/0.99  sup_time_sim_immed:                     0.
% 1.03/0.99  
% 1.03/0.99  sup_num_of_clauses:                     8
% 1.03/0.99  sup_num_in_active:                      4
% 1.03/0.99  sup_num_in_passive:                     4
% 1.03/0.99  sup_num_of_loops:                       4
% 1.03/0.99  sup_fw_superposition:                   0
% 1.03/0.99  sup_bw_superposition:                   0
% 1.03/0.99  sup_immediate_simplified:               0
% 1.03/0.99  sup_given_eliminated:                   0
% 1.03/0.99  comparisons_done:                       0
% 1.03/0.99  comparisons_avoided:                    0
% 1.03/0.99  
% 1.03/0.99  ------ Simplifications
% 1.03/0.99  
% 1.03/0.99  
% 1.03/0.99  sim_fw_subset_subsumed:                 0
% 1.03/0.99  sim_bw_subset_subsumed:                 0
% 1.03/0.99  sim_fw_subsumed:                        0
% 1.03/0.99  sim_bw_subsumed:                        0
% 1.03/0.99  sim_fw_subsumption_res:                 0
% 1.03/0.99  sim_bw_subsumption_res:                 0
% 1.03/0.99  sim_tautology_del:                      0
% 1.03/0.99  sim_eq_tautology_del:                   0
% 1.03/0.99  sim_eq_res_simp:                        1
% 1.03/0.99  sim_fw_demodulated:                     1
% 1.03/0.99  sim_bw_demodulated:                     0
% 1.03/0.99  sim_light_normalised:                   3
% 1.03/0.99  sim_joinable_taut:                      0
% 1.03/0.99  sim_joinable_simp:                      0
% 1.03/0.99  sim_ac_normalised:                      0
% 1.03/0.99  sim_smt_subsumption:                    0
% 1.03/0.99  
%------------------------------------------------------------------------------
