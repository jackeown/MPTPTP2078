%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:55 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  180 (1000 expanded)
%              Number of clauses        :  108 ( 277 expanded)
%              Number of leaves         :   16 ( 228 expanded)
%              Depth                    :   27
%              Number of atoms          :  816 (7333 expanded)
%              Number of equality atoms :  124 ( 169 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
           => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
             => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) )
             => v4_pre_topc(k6_waybel_0(X0,X1),X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_pre_topc(k6_waybel_0(X0,sK2),X0)
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
            & ! [X2] :
                ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(sK1,X1),sK1)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_waybel_9(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v3_orders_2(sK1)
      & v8_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_9(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v3_orders_2(sK1)
    & v8_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f46,f45])).

fof(f75,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1387,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1720,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_52,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_27,c_26,c_23,c_52])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),k6_domain_1(u1_struct_0(sK1),X0_57)) = k6_waybel_0(sK1,X0_57) ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_1723,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),k6_domain_1(u1_struct_0(sK1),X0_57)) = k6_waybel_0(sK1,X0_57)
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1944,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1720,c_1723])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_359,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_360,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_666,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_360])).

cnf(c_667,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_25,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_70,plain,
    ( ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_25,c_23,c_52,c_70])).

cnf(c_672,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_671])).

cnf(c_729,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k4_waybel_1(sK1,X4) != X0
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_672])).

cnf(c_730,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_360])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_734,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ v4_pre_topc(X3,X2)
    | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_25,c_23,c_52,c_70,c_685])).

cnf(c_735,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_1381,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_57),X0_58,X1_58)
    | ~ v4_pre_topc(X1_57,X1_58)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),k4_waybel_1(sK1,X0_57),X1_57),X0_58)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X1_58)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X0_58)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | u1_struct_0(X0_58) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_735])).

cnf(c_1728,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK1)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_57),X1_58,X0_58) != iProver_top
    | v4_pre_topc(X1_57,X0_58) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),X1_58) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_2351,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
    | v4_pre_topc(X1_57,X0_58) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1728])).

cnf(c_36,plain,
    ( l1_waybel_9(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_48,plain,
    ( l1_waybel_9(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_50,plain,
    ( l1_waybel_9(sK1) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_2479,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
    | v4_pre_topc(X1_57,X0_58) != iProver_top
    | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
    | u1_struct_0(X0_58) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_36,c_50])).

cnf(c_2480,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
    | v4_pre_topc(X1_57,X0_58) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_2479])).

cnf(c_2491,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1) != iProver_top
    | v4_pre_topc(X1_57,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2480])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1388,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1428,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_360])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_25,c_23,c_52,c_70])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_1382,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_708])).

cnf(c_1446,plain,
    ( m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_2579,plain,
    ( v4_pre_topc(X1_57,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_36,c_50,c_1428,c_1446])).

cnf(c_2580,plain,
    ( v4_pre_topc(X0_57,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_57),X0_57),sK1) = iProver_top
    | m1_subset_1(X1_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2579])).

cnf(c_2589,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_2580])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | m1_subset_1(k8_relset_1(X0_59,X1_59,X0_57,X1_57),k1_zfmisc_1(X0_59)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1716,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
    | m1_subset_1(k8_relset_1(X0_59,X1_59,X0_57,X1_57),k1_zfmisc_1(X0_59)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_2039,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_1716])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,k6_waybel_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_435,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(X4)
    | X2 != X5
    | k6_waybel_0(X0,X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_436,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(X3))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(X3) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_9,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_508,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_509,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_513,plain,
    ( r3_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_25,c_23,c_52,c_70])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_529,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_530,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r3_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_25,c_23,c_52,c_70])).

cnf(c_592,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X0 != X2
    | X1 != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_513,c_534])).

cnf(c_593,plain,
    ( r1_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(X5))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(X5)
    | X3 != X2
    | X3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_593])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(X2))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_xboole_0(X2) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_25,c_23,c_52,c_70])).

cnf(c_1383,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
    | ~ v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_616])).

cnf(c_1393,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
    | ~ v1_xboole_0(X0_59)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1383])).

cnf(c_1394,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1383])).

cnf(c_1392,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1383])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_1497,plain,
    ( ~ v1_xboole_0(X0_59)
    | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1393,c_22,c_1394,c_1444])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
    | ~ v1_xboole_0(X0_59) ),
    inference(renaming,[status(thm)],[c_1497])).

cnf(c_1929,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_1930,plain,
    ( m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_1932,plain,
    ( m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(X0_57,X0_59)
    | m1_subset_1(k6_domain_1(X0_59,X0_57),k1_zfmisc_1(X0_59))
    | v1_xboole_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1885,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_1886,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_1448,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_18,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_392,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_393,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_49,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_29,c_25,c_23,c_49,c_52,c_70])).

cnf(c_398,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_1385,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_57),sK1)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1433,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_57),sK1) = iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_1435,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_20,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2589,c_2039,c_1932,c_1886,c_1448,c_1435,c_41,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.35/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/0.97  
% 1.35/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.35/0.97  
% 1.35/0.97  ------  iProver source info
% 1.35/0.97  
% 1.35/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.35/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.35/0.97  git: non_committed_changes: false
% 1.35/0.97  git: last_make_outside_of_git: false
% 1.35/0.97  
% 1.35/0.97  ------ 
% 1.35/0.97  
% 1.35/0.97  ------ Input Options
% 1.35/0.97  
% 1.35/0.97  --out_options                           all
% 1.35/0.97  --tptp_safe_out                         true
% 1.35/0.97  --problem_path                          ""
% 1.35/0.97  --include_path                          ""
% 1.35/0.97  --clausifier                            res/vclausify_rel
% 1.35/0.97  --clausifier_options                    --mode clausify
% 1.35/0.97  --stdin                                 false
% 1.35/0.97  --stats_out                             all
% 1.35/0.97  
% 1.35/0.97  ------ General Options
% 1.35/0.97  
% 1.35/0.97  --fof                                   false
% 1.35/0.97  --time_out_real                         305.
% 1.35/0.97  --time_out_virtual                      -1.
% 1.35/0.97  --symbol_type_check                     false
% 1.35/0.97  --clausify_out                          false
% 1.35/0.97  --sig_cnt_out                           false
% 1.35/0.97  --trig_cnt_out                          false
% 1.35/0.97  --trig_cnt_out_tolerance                1.
% 1.35/0.97  --trig_cnt_out_sk_spl                   false
% 1.35/0.97  --abstr_cl_out                          false
% 1.35/0.97  
% 1.35/0.97  ------ Global Options
% 1.35/0.97  
% 1.35/0.97  --schedule                              default
% 1.35/0.97  --add_important_lit                     false
% 1.35/0.97  --prop_solver_per_cl                    1000
% 1.35/0.97  --min_unsat_core                        false
% 1.35/0.97  --soft_assumptions                      false
% 1.35/0.97  --soft_lemma_size                       3
% 1.35/0.97  --prop_impl_unit_size                   0
% 1.35/0.97  --prop_impl_unit                        []
% 1.35/0.97  --share_sel_clauses                     true
% 1.35/0.97  --reset_solvers                         false
% 1.35/0.97  --bc_imp_inh                            [conj_cone]
% 1.35/0.97  --conj_cone_tolerance                   3.
% 1.35/0.97  --extra_neg_conj                        none
% 1.35/0.97  --large_theory_mode                     true
% 1.35/0.97  --prolific_symb_bound                   200
% 1.35/0.97  --lt_threshold                          2000
% 1.35/0.97  --clause_weak_htbl                      true
% 1.35/0.97  --gc_record_bc_elim                     false
% 1.35/0.97  
% 1.35/0.97  ------ Preprocessing Options
% 1.35/0.97  
% 1.35/0.97  --preprocessing_flag                    true
% 1.35/0.97  --time_out_prep_mult                    0.1
% 1.35/0.97  --splitting_mode                        input
% 1.35/0.97  --splitting_grd                         true
% 1.35/0.97  --splitting_cvd                         false
% 1.35/0.97  --splitting_cvd_svl                     false
% 1.35/0.97  --splitting_nvd                         32
% 1.35/0.97  --sub_typing                            true
% 1.35/0.97  --prep_gs_sim                           true
% 1.35/0.97  --prep_unflatten                        true
% 1.35/0.97  --prep_res_sim                          true
% 1.35/0.97  --prep_upred                            true
% 1.35/0.97  --prep_sem_filter                       exhaustive
% 1.35/0.97  --prep_sem_filter_out                   false
% 1.35/0.97  --pred_elim                             true
% 1.35/0.97  --res_sim_input                         true
% 1.35/0.97  --eq_ax_congr_red                       true
% 1.35/0.97  --pure_diseq_elim                       true
% 1.35/0.97  --brand_transform                       false
% 1.35/0.97  --non_eq_to_eq                          false
% 1.35/0.97  --prep_def_merge                        true
% 1.35/0.97  --prep_def_merge_prop_impl              false
% 1.35/0.97  --prep_def_merge_mbd                    true
% 1.35/0.97  --prep_def_merge_tr_red                 false
% 1.35/0.97  --prep_def_merge_tr_cl                  false
% 1.35/0.97  --smt_preprocessing                     true
% 1.35/0.97  --smt_ac_axioms                         fast
% 1.35/0.97  --preprocessed_out                      false
% 1.35/0.97  --preprocessed_stats                    false
% 1.35/0.97  
% 1.35/0.97  ------ Abstraction refinement Options
% 1.35/0.97  
% 1.35/0.97  --abstr_ref                             []
% 1.35/0.97  --abstr_ref_prep                        false
% 1.35/0.97  --abstr_ref_until_sat                   false
% 1.35/0.97  --abstr_ref_sig_restrict                funpre
% 1.35/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/0.97  --abstr_ref_under                       []
% 1.35/0.97  
% 1.35/0.97  ------ SAT Options
% 1.35/0.97  
% 1.35/0.97  --sat_mode                              false
% 1.35/0.97  --sat_fm_restart_options                ""
% 1.35/0.97  --sat_gr_def                            false
% 1.35/0.97  --sat_epr_types                         true
% 1.35/0.97  --sat_non_cyclic_types                  false
% 1.35/0.97  --sat_finite_models                     false
% 1.35/0.97  --sat_fm_lemmas                         false
% 1.35/0.97  --sat_fm_prep                           false
% 1.35/0.98  --sat_fm_uc_incr                        true
% 1.35/0.98  --sat_out_model                         small
% 1.35/0.98  --sat_out_clauses                       false
% 1.35/0.98  
% 1.35/0.98  ------ QBF Options
% 1.35/0.98  
% 1.35/0.98  --qbf_mode                              false
% 1.35/0.98  --qbf_elim_univ                         false
% 1.35/0.98  --qbf_dom_inst                          none
% 1.35/0.98  --qbf_dom_pre_inst                      false
% 1.35/0.98  --qbf_sk_in                             false
% 1.35/0.98  --qbf_pred_elim                         true
% 1.35/0.98  --qbf_split                             512
% 1.35/0.98  
% 1.35/0.98  ------ BMC1 Options
% 1.35/0.98  
% 1.35/0.98  --bmc1_incremental                      false
% 1.35/0.98  --bmc1_axioms                           reachable_all
% 1.35/0.98  --bmc1_min_bound                        0
% 1.35/0.98  --bmc1_max_bound                        -1
% 1.35/0.98  --bmc1_max_bound_default                -1
% 1.35/0.98  --bmc1_symbol_reachability              true
% 1.35/0.98  --bmc1_property_lemmas                  false
% 1.35/0.98  --bmc1_k_induction                      false
% 1.35/0.98  --bmc1_non_equiv_states                 false
% 1.35/0.98  --bmc1_deadlock                         false
% 1.35/0.98  --bmc1_ucm                              false
% 1.35/0.98  --bmc1_add_unsat_core                   none
% 1.35/0.98  --bmc1_unsat_core_children              false
% 1.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/0.98  --bmc1_out_stat                         full
% 1.35/0.98  --bmc1_ground_init                      false
% 1.35/0.98  --bmc1_pre_inst_next_state              false
% 1.35/0.98  --bmc1_pre_inst_state                   false
% 1.35/0.98  --bmc1_pre_inst_reach_state             false
% 1.35/0.98  --bmc1_out_unsat_core                   false
% 1.35/0.98  --bmc1_aig_witness_out                  false
% 1.35/0.98  --bmc1_verbose                          false
% 1.35/0.98  --bmc1_dump_clauses_tptp                false
% 1.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.35/0.98  --bmc1_dump_file                        -
% 1.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.35/0.98  --bmc1_ucm_extend_mode                  1
% 1.35/0.98  --bmc1_ucm_init_mode                    2
% 1.35/0.98  --bmc1_ucm_cone_mode                    none
% 1.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.35/0.98  --bmc1_ucm_relax_model                  4
% 1.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/0.98  --bmc1_ucm_layered_model                none
% 1.35/0.98  --bmc1_ucm_max_lemma_size               10
% 1.35/0.98  
% 1.35/0.98  ------ AIG Options
% 1.35/0.98  
% 1.35/0.98  --aig_mode                              false
% 1.35/0.98  
% 1.35/0.98  ------ Instantiation Options
% 1.35/0.98  
% 1.35/0.98  --instantiation_flag                    true
% 1.35/0.98  --inst_sos_flag                         false
% 1.35/0.98  --inst_sos_phase                        true
% 1.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel_side                     num_symb
% 1.35/0.98  --inst_solver_per_active                1400
% 1.35/0.98  --inst_solver_calls_frac                1.
% 1.35/0.98  --inst_passive_queue_type               priority_queues
% 1.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/0.98  --inst_passive_queues_freq              [25;2]
% 1.35/0.98  --inst_dismatching                      true
% 1.35/0.98  --inst_eager_unprocessed_to_passive     true
% 1.35/0.98  --inst_prop_sim_given                   true
% 1.35/0.98  --inst_prop_sim_new                     false
% 1.35/0.98  --inst_subs_new                         false
% 1.35/0.98  --inst_eq_res_simp                      false
% 1.35/0.98  --inst_subs_given                       false
% 1.35/0.98  --inst_orphan_elimination               true
% 1.35/0.98  --inst_learning_loop_flag               true
% 1.35/0.98  --inst_learning_start                   3000
% 1.35/0.98  --inst_learning_factor                  2
% 1.35/0.98  --inst_start_prop_sim_after_learn       3
% 1.35/0.98  --inst_sel_renew                        solver
% 1.35/0.98  --inst_lit_activity_flag                true
% 1.35/0.98  --inst_restr_to_given                   false
% 1.35/0.98  --inst_activity_threshold               500
% 1.35/0.98  --inst_out_proof                        true
% 1.35/0.98  
% 1.35/0.98  ------ Resolution Options
% 1.35/0.98  
% 1.35/0.98  --resolution_flag                       true
% 1.35/0.98  --res_lit_sel                           adaptive
% 1.35/0.98  --res_lit_sel_side                      none
% 1.35/0.98  --res_ordering                          kbo
% 1.35/0.98  --res_to_prop_solver                    active
% 1.35/0.98  --res_prop_simpl_new                    false
% 1.35/0.98  --res_prop_simpl_given                  true
% 1.35/0.98  --res_passive_queue_type                priority_queues
% 1.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/0.98  --res_passive_queues_freq               [15;5]
% 1.35/0.98  --res_forward_subs                      full
% 1.35/0.98  --res_backward_subs                     full
% 1.35/0.98  --res_forward_subs_resolution           true
% 1.35/0.98  --res_backward_subs_resolution          true
% 1.35/0.98  --res_orphan_elimination                true
% 1.35/0.98  --res_time_limit                        2.
% 1.35/0.98  --res_out_proof                         true
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Options
% 1.35/0.98  
% 1.35/0.98  --superposition_flag                    true
% 1.35/0.98  --sup_passive_queue_type                priority_queues
% 1.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.35/0.98  --demod_completeness_check              fast
% 1.35/0.98  --demod_use_ground                      true
% 1.35/0.98  --sup_to_prop_solver                    passive
% 1.35/0.98  --sup_prop_simpl_new                    true
% 1.35/0.98  --sup_prop_simpl_given                  true
% 1.35/0.98  --sup_fun_splitting                     false
% 1.35/0.98  --sup_smt_interval                      50000
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Simplification Setup
% 1.35/0.98  
% 1.35/0.98  --sup_indices_passive                   []
% 1.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_full_bw                           [BwDemod]
% 1.35/0.98  --sup_immed_triv                        [TrivRules]
% 1.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_immed_bw_main                     []
% 1.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.98  
% 1.35/0.98  ------ Combination Options
% 1.35/0.98  
% 1.35/0.98  --comb_res_mult                         3
% 1.35/0.98  --comb_sup_mult                         2
% 1.35/0.98  --comb_inst_mult                        10
% 1.35/0.98  
% 1.35/0.98  ------ Debug Options
% 1.35/0.98  
% 1.35/0.98  --dbg_backtrace                         false
% 1.35/0.98  --dbg_dump_prop_clauses                 false
% 1.35/0.98  --dbg_dump_prop_clauses_file            -
% 1.35/0.98  --dbg_out_stat                          false
% 1.35/0.98  ------ Parsing...
% 1.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.35/0.98  ------ Proving...
% 1.35/0.98  ------ Problem Properties 
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  clauses                                 16
% 1.35/0.98  conjectures                             3
% 1.35/0.98  EPR                                     2
% 1.35/0.98  Horn                                    12
% 1.35/0.98  unary                                   3
% 1.35/0.98  binary                                  7
% 1.35/0.98  lits                                    58
% 1.35/0.98  lits eq                                 9
% 1.35/0.98  fd_pure                                 0
% 1.35/0.98  fd_pseudo                               0
% 1.35/0.98  fd_cond                                 0
% 1.35/0.98  fd_pseudo_cond                          0
% 1.35/0.98  AC symbols                              0
% 1.35/0.98  
% 1.35/0.98  ------ Schedule dynamic 5 is on 
% 1.35/0.98  
% 1.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  ------ 
% 1.35/0.98  Current options:
% 1.35/0.98  ------ 
% 1.35/0.98  
% 1.35/0.98  ------ Input Options
% 1.35/0.98  
% 1.35/0.98  --out_options                           all
% 1.35/0.98  --tptp_safe_out                         true
% 1.35/0.98  --problem_path                          ""
% 1.35/0.98  --include_path                          ""
% 1.35/0.98  --clausifier                            res/vclausify_rel
% 1.35/0.98  --clausifier_options                    --mode clausify
% 1.35/0.98  --stdin                                 false
% 1.35/0.98  --stats_out                             all
% 1.35/0.98  
% 1.35/0.98  ------ General Options
% 1.35/0.98  
% 1.35/0.98  --fof                                   false
% 1.35/0.98  --time_out_real                         305.
% 1.35/0.98  --time_out_virtual                      -1.
% 1.35/0.98  --symbol_type_check                     false
% 1.35/0.98  --clausify_out                          false
% 1.35/0.98  --sig_cnt_out                           false
% 1.35/0.98  --trig_cnt_out                          false
% 1.35/0.98  --trig_cnt_out_tolerance                1.
% 1.35/0.98  --trig_cnt_out_sk_spl                   false
% 1.35/0.98  --abstr_cl_out                          false
% 1.35/0.98  
% 1.35/0.98  ------ Global Options
% 1.35/0.98  
% 1.35/0.98  --schedule                              default
% 1.35/0.98  --add_important_lit                     false
% 1.35/0.98  --prop_solver_per_cl                    1000
% 1.35/0.98  --min_unsat_core                        false
% 1.35/0.98  --soft_assumptions                      false
% 1.35/0.98  --soft_lemma_size                       3
% 1.35/0.98  --prop_impl_unit_size                   0
% 1.35/0.98  --prop_impl_unit                        []
% 1.35/0.98  --share_sel_clauses                     true
% 1.35/0.98  --reset_solvers                         false
% 1.35/0.98  --bc_imp_inh                            [conj_cone]
% 1.35/0.98  --conj_cone_tolerance                   3.
% 1.35/0.98  --extra_neg_conj                        none
% 1.35/0.98  --large_theory_mode                     true
% 1.35/0.98  --prolific_symb_bound                   200
% 1.35/0.98  --lt_threshold                          2000
% 1.35/0.98  --clause_weak_htbl                      true
% 1.35/0.98  --gc_record_bc_elim                     false
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing Options
% 1.35/0.98  
% 1.35/0.98  --preprocessing_flag                    true
% 1.35/0.98  --time_out_prep_mult                    0.1
% 1.35/0.98  --splitting_mode                        input
% 1.35/0.98  --splitting_grd                         true
% 1.35/0.98  --splitting_cvd                         false
% 1.35/0.98  --splitting_cvd_svl                     false
% 1.35/0.98  --splitting_nvd                         32
% 1.35/0.98  --sub_typing                            true
% 1.35/0.98  --prep_gs_sim                           true
% 1.35/0.98  --prep_unflatten                        true
% 1.35/0.98  --prep_res_sim                          true
% 1.35/0.98  --prep_upred                            true
% 1.35/0.98  --prep_sem_filter                       exhaustive
% 1.35/0.98  --prep_sem_filter_out                   false
% 1.35/0.98  --pred_elim                             true
% 1.35/0.98  --res_sim_input                         true
% 1.35/0.98  --eq_ax_congr_red                       true
% 1.35/0.98  --pure_diseq_elim                       true
% 1.35/0.98  --brand_transform                       false
% 1.35/0.98  --non_eq_to_eq                          false
% 1.35/0.98  --prep_def_merge                        true
% 1.35/0.98  --prep_def_merge_prop_impl              false
% 1.35/0.98  --prep_def_merge_mbd                    true
% 1.35/0.98  --prep_def_merge_tr_red                 false
% 1.35/0.98  --prep_def_merge_tr_cl                  false
% 1.35/0.98  --smt_preprocessing                     true
% 1.35/0.98  --smt_ac_axioms                         fast
% 1.35/0.98  --preprocessed_out                      false
% 1.35/0.98  --preprocessed_stats                    false
% 1.35/0.98  
% 1.35/0.98  ------ Abstraction refinement Options
% 1.35/0.98  
% 1.35/0.98  --abstr_ref                             []
% 1.35/0.98  --abstr_ref_prep                        false
% 1.35/0.98  --abstr_ref_until_sat                   false
% 1.35/0.98  --abstr_ref_sig_restrict                funpre
% 1.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/0.98  --abstr_ref_under                       []
% 1.35/0.98  
% 1.35/0.98  ------ SAT Options
% 1.35/0.98  
% 1.35/0.98  --sat_mode                              false
% 1.35/0.98  --sat_fm_restart_options                ""
% 1.35/0.98  --sat_gr_def                            false
% 1.35/0.98  --sat_epr_types                         true
% 1.35/0.98  --sat_non_cyclic_types                  false
% 1.35/0.98  --sat_finite_models                     false
% 1.35/0.98  --sat_fm_lemmas                         false
% 1.35/0.98  --sat_fm_prep                           false
% 1.35/0.98  --sat_fm_uc_incr                        true
% 1.35/0.98  --sat_out_model                         small
% 1.35/0.98  --sat_out_clauses                       false
% 1.35/0.98  
% 1.35/0.98  ------ QBF Options
% 1.35/0.98  
% 1.35/0.98  --qbf_mode                              false
% 1.35/0.98  --qbf_elim_univ                         false
% 1.35/0.98  --qbf_dom_inst                          none
% 1.35/0.98  --qbf_dom_pre_inst                      false
% 1.35/0.98  --qbf_sk_in                             false
% 1.35/0.98  --qbf_pred_elim                         true
% 1.35/0.98  --qbf_split                             512
% 1.35/0.98  
% 1.35/0.98  ------ BMC1 Options
% 1.35/0.98  
% 1.35/0.98  --bmc1_incremental                      false
% 1.35/0.98  --bmc1_axioms                           reachable_all
% 1.35/0.98  --bmc1_min_bound                        0
% 1.35/0.98  --bmc1_max_bound                        -1
% 1.35/0.98  --bmc1_max_bound_default                -1
% 1.35/0.98  --bmc1_symbol_reachability              true
% 1.35/0.98  --bmc1_property_lemmas                  false
% 1.35/0.98  --bmc1_k_induction                      false
% 1.35/0.98  --bmc1_non_equiv_states                 false
% 1.35/0.98  --bmc1_deadlock                         false
% 1.35/0.98  --bmc1_ucm                              false
% 1.35/0.98  --bmc1_add_unsat_core                   none
% 1.35/0.98  --bmc1_unsat_core_children              false
% 1.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/0.98  --bmc1_out_stat                         full
% 1.35/0.98  --bmc1_ground_init                      false
% 1.35/0.98  --bmc1_pre_inst_next_state              false
% 1.35/0.98  --bmc1_pre_inst_state                   false
% 1.35/0.98  --bmc1_pre_inst_reach_state             false
% 1.35/0.98  --bmc1_out_unsat_core                   false
% 1.35/0.98  --bmc1_aig_witness_out                  false
% 1.35/0.98  --bmc1_verbose                          false
% 1.35/0.98  --bmc1_dump_clauses_tptp                false
% 1.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.35/0.98  --bmc1_dump_file                        -
% 1.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.35/0.98  --bmc1_ucm_extend_mode                  1
% 1.35/0.98  --bmc1_ucm_init_mode                    2
% 1.35/0.98  --bmc1_ucm_cone_mode                    none
% 1.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.35/0.98  --bmc1_ucm_relax_model                  4
% 1.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/0.98  --bmc1_ucm_layered_model                none
% 1.35/0.98  --bmc1_ucm_max_lemma_size               10
% 1.35/0.98  
% 1.35/0.98  ------ AIG Options
% 1.35/0.98  
% 1.35/0.98  --aig_mode                              false
% 1.35/0.98  
% 1.35/0.98  ------ Instantiation Options
% 1.35/0.98  
% 1.35/0.98  --instantiation_flag                    true
% 1.35/0.98  --inst_sos_flag                         false
% 1.35/0.98  --inst_sos_phase                        true
% 1.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel_side                     none
% 1.35/0.98  --inst_solver_per_active                1400
% 1.35/0.98  --inst_solver_calls_frac                1.
% 1.35/0.98  --inst_passive_queue_type               priority_queues
% 1.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/0.98  --inst_passive_queues_freq              [25;2]
% 1.35/0.98  --inst_dismatching                      true
% 1.35/0.98  --inst_eager_unprocessed_to_passive     true
% 1.35/0.98  --inst_prop_sim_given                   true
% 1.35/0.98  --inst_prop_sim_new                     false
% 1.35/0.98  --inst_subs_new                         false
% 1.35/0.98  --inst_eq_res_simp                      false
% 1.35/0.98  --inst_subs_given                       false
% 1.35/0.98  --inst_orphan_elimination               true
% 1.35/0.98  --inst_learning_loop_flag               true
% 1.35/0.98  --inst_learning_start                   3000
% 1.35/0.98  --inst_learning_factor                  2
% 1.35/0.98  --inst_start_prop_sim_after_learn       3
% 1.35/0.98  --inst_sel_renew                        solver
% 1.35/0.98  --inst_lit_activity_flag                true
% 1.35/0.98  --inst_restr_to_given                   false
% 1.35/0.98  --inst_activity_threshold               500
% 1.35/0.98  --inst_out_proof                        true
% 1.35/0.98  
% 1.35/0.98  ------ Resolution Options
% 1.35/0.98  
% 1.35/0.98  --resolution_flag                       false
% 1.35/0.98  --res_lit_sel                           adaptive
% 1.35/0.98  --res_lit_sel_side                      none
% 1.35/0.98  --res_ordering                          kbo
% 1.35/0.98  --res_to_prop_solver                    active
% 1.35/0.98  --res_prop_simpl_new                    false
% 1.35/0.98  --res_prop_simpl_given                  true
% 1.35/0.98  --res_passive_queue_type                priority_queues
% 1.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/0.98  --res_passive_queues_freq               [15;5]
% 1.35/0.98  --res_forward_subs                      full
% 1.35/0.98  --res_backward_subs                     full
% 1.35/0.98  --res_forward_subs_resolution           true
% 1.35/0.98  --res_backward_subs_resolution          true
% 1.35/0.98  --res_orphan_elimination                true
% 1.35/0.98  --res_time_limit                        2.
% 1.35/0.98  --res_out_proof                         true
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Options
% 1.35/0.98  
% 1.35/0.98  --superposition_flag                    true
% 1.35/0.98  --sup_passive_queue_type                priority_queues
% 1.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.35/0.98  --demod_completeness_check              fast
% 1.35/0.98  --demod_use_ground                      true
% 1.35/0.98  --sup_to_prop_solver                    passive
% 1.35/0.98  --sup_prop_simpl_new                    true
% 1.35/0.98  --sup_prop_simpl_given                  true
% 1.35/0.98  --sup_fun_splitting                     false
% 1.35/0.98  --sup_smt_interval                      50000
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Simplification Setup
% 1.35/0.98  
% 1.35/0.98  --sup_indices_passive                   []
% 1.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_full_bw                           [BwDemod]
% 1.35/0.98  --sup_immed_triv                        [TrivRules]
% 1.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_immed_bw_main                     []
% 1.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.98  
% 1.35/0.98  ------ Combination Options
% 1.35/0.98  
% 1.35/0.98  --comb_res_mult                         3
% 1.35/0.98  --comb_sup_mult                         2
% 1.35/0.98  --comb_inst_mult                        10
% 1.35/0.98  
% 1.35/0.98  ------ Debug Options
% 1.35/0.98  
% 1.35/0.98  --dbg_backtrace                         false
% 1.35/0.98  --dbg_dump_prop_clauses                 false
% 1.35/0.98  --dbg_dump_prop_clauses_file            -
% 1.35/0.98  --dbg_out_stat                          false
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  ------ Proving...
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  % SZS status Theorem for theBenchmark.p
% 1.35/0.98  
% 1.35/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.35/0.98  
% 1.35/0.98  fof(f13,conjecture,(
% 1.35/0.98    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f14,negated_conjecture,(
% 1.35/0.98    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.35/0.98    inference(negated_conjecture,[],[f13])).
% 1.35/0.98  
% 1.35/0.98  fof(f15,plain,(
% 1.35/0.98    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.35/0.98    inference(pure_predicate_removal,[],[f14])).
% 1.35/0.98  
% 1.35/0.98  fof(f37,plain,(
% 1.35/0.98    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f15])).
% 1.35/0.98  
% 1.35/0.98  fof(f38,plain,(
% 1.35/0.98    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.35/0.98    inference(flattening,[],[f37])).
% 1.35/0.98  
% 1.35/0.98  fof(f46,plain,(
% 1.35/0.98    ( ! [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k6_waybel_0(X0,sK2),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.35/0.98    introduced(choice_axiom,[])).
% 1.35/0.98  
% 1.35/0.98  fof(f45,plain,(
% 1.35/0.98    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK1,X1),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.35/0.98    introduced(choice_axiom,[])).
% 1.35/0.98  
% 1.35/0.98  fof(f47,plain,(
% 1.35/0.98    (~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f46,f45])).
% 1.35/0.98  
% 1.35/0.98  fof(f75,plain,(
% 1.35/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f12,axiom,(
% 1.35/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f35,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f12])).
% 1.35/0.98  
% 1.35/0.98  fof(f36,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.35/0.98    inference(flattening,[],[f35])).
% 1.35/0.98  
% 1.35/0.98  fof(f67,plain,(
% 1.35/0.98    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f36])).
% 1.35/0.98  
% 1.35/0.98  fof(f73,plain,(
% 1.35/0.98    v2_lattice3(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f70,plain,(
% 1.35/0.98    v3_orders_2(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f71,plain,(
% 1.35/0.98    v5_orders_2(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f74,plain,(
% 1.35/0.98    l1_waybel_9(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f10,axiom,(
% 1.35/0.98    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f32,plain,(
% 1.35/0.98    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.35/0.98    inference(ennf_transformation,[],[f10])).
% 1.35/0.98  
% 1.35/0.98  fof(f65,plain,(
% 1.35/0.98    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f32])).
% 1.35/0.98  
% 1.35/0.98  fof(f3,axiom,(
% 1.35/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f18,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.98    inference(ennf_transformation,[],[f3])).
% 1.35/0.98  
% 1.35/0.98  fof(f19,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.98    inference(flattening,[],[f18])).
% 1.35/0.98  
% 1.35/0.98  fof(f39,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.98    inference(nnf_transformation,[],[f19])).
% 1.35/0.98  
% 1.35/0.98  fof(f40,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.98    inference(rectify,[],[f39])).
% 1.35/0.98  
% 1.35/0.98  fof(f41,plain,(
% 1.35/0.98    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.35/0.98    introduced(choice_axiom,[])).
% 1.35/0.98  
% 1.35/0.98  fof(f42,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 1.35/0.98  
% 1.35/0.98  fof(f50,plain,(
% 1.35/0.98    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f42])).
% 1.35/0.98  
% 1.35/0.98  fof(f9,axiom,(
% 1.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f30,plain,(
% 1.35/0.98    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f9])).
% 1.35/0.98  
% 1.35/0.98  fof(f31,plain,(
% 1.35/0.98    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(flattening,[],[f30])).
% 1.35/0.98  
% 1.35/0.98  fof(f62,plain,(
% 1.35/0.98    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f31])).
% 1.35/0.98  
% 1.35/0.98  fof(f72,plain,(
% 1.35/0.98    v1_lattice3(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f7,axiom,(
% 1.35/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f26,plain,(
% 1.35/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.35/0.98    inference(ennf_transformation,[],[f7])).
% 1.35/0.98  
% 1.35/0.98  fof(f27,plain,(
% 1.35/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.35/0.98    inference(flattening,[],[f26])).
% 1.35/0.98  
% 1.35/0.98  fof(f58,plain,(
% 1.35/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f27])).
% 1.35/0.98  
% 1.35/0.98  fof(f61,plain,(
% 1.35/0.98    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f31])).
% 1.35/0.98  
% 1.35/0.98  fof(f64,plain,(
% 1.35/0.98    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f32])).
% 1.35/0.98  
% 1.35/0.98  fof(f76,plain,(
% 1.35/0.98    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f63,plain,(
% 1.35/0.98    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f31])).
% 1.35/0.98  
% 1.35/0.98  fof(f2,axiom,(
% 1.35/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f17,plain,(
% 1.35/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.98    inference(ennf_transformation,[],[f2])).
% 1.35/0.98  
% 1.35/0.98  fof(f49,plain,(
% 1.35/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.98    inference(cnf_transformation,[],[f17])).
% 1.35/0.98  
% 1.35/0.98  fof(f1,axiom,(
% 1.35/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f16,plain,(
% 1.35/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.98    inference(ennf_transformation,[],[f1])).
% 1.35/0.98  
% 1.35/0.98  fof(f48,plain,(
% 1.35/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f16])).
% 1.35/0.98  
% 1.35/0.98  fof(f8,axiom,(
% 1.35/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)))))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f28,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f8])).
% 1.35/0.98  
% 1.35/0.98  fof(f29,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k6_waybel_0(X0,X1)) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(flattening,[],[f28])).
% 1.35/0.98  
% 1.35/0.98  fof(f44,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k6_waybel_0(X0,X1)) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,k6_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(nnf_transformation,[],[f29])).
% 1.35/0.98  
% 1.35/0.98  fof(f60,plain,(
% 1.35/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k6_waybel_0(X0,X1)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f44])).
% 1.35/0.98  
% 1.35/0.98  fof(f6,axiom,(
% 1.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f24,plain,(
% 1.35/0.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f6])).
% 1.35/0.98  
% 1.35/0.98  fof(f25,plain,(
% 1.35/0.98    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(flattening,[],[f24])).
% 1.35/0.98  
% 1.35/0.98  fof(f57,plain,(
% 1.35/0.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f25])).
% 1.35/0.98  
% 1.35/0.98  fof(f5,axiom,(
% 1.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f22,plain,(
% 1.35/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f5])).
% 1.35/0.98  
% 1.35/0.98  fof(f23,plain,(
% 1.35/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(flattening,[],[f22])).
% 1.35/0.98  
% 1.35/0.98  fof(f43,plain,(
% 1.35/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(nnf_transformation,[],[f23])).
% 1.35/0.98  
% 1.35/0.98  fof(f55,plain,(
% 1.35/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f43])).
% 1.35/0.98  
% 1.35/0.98  fof(f4,axiom,(
% 1.35/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f20,plain,(
% 1.35/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f4])).
% 1.35/0.98  
% 1.35/0.98  fof(f21,plain,(
% 1.35/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.35/0.98    inference(flattening,[],[f20])).
% 1.35/0.98  
% 1.35/0.98  fof(f54,plain,(
% 1.35/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f21])).
% 1.35/0.98  
% 1.35/0.98  fof(f11,axiom,(
% 1.35/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.35/0.98  
% 1.35/0.98  fof(f33,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.98    inference(ennf_transformation,[],[f11])).
% 1.35/0.98  
% 1.35/0.98  fof(f34,plain,(
% 1.35/0.98    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.98    inference(flattening,[],[f33])).
% 1.35/0.98  
% 1.35/0.98  fof(f66,plain,(
% 1.35/0.98    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.98    inference(cnf_transformation,[],[f34])).
% 1.35/0.98  
% 1.35/0.98  fof(f69,plain,(
% 1.35/0.98    v8_pre_topc(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f68,plain,(
% 1.35/0.98    v2_pre_topc(sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  fof(f77,plain,(
% 1.35/0.98    ~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)),
% 1.35/0.98    inference(cnf_transformation,[],[f47])).
% 1.35/0.98  
% 1.35/0.98  cnf(c_22,negated_conjecture,
% 1.35/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(cnf_transformation,[],[f75]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1387,negated_conjecture,
% 1.35/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1720,plain,
% 1.35/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_19,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | ~ v5_orders_2(X1)
% 1.35/0.98      | ~ v2_lattice3(X1)
% 1.35/0.98      | ~ v3_orders_2(X1)
% 1.35/0.98      | ~ l1_orders_2(X1)
% 1.35/0.98      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_24,negated_conjecture,
% 1.35/0.98      ( v2_lattice3(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_413,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | ~ v5_orders_2(X1)
% 1.35/0.98      | ~ v3_orders_2(X1)
% 1.35/0.98      | ~ l1_orders_2(X1)
% 1.35/0.98      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
% 1.35/0.98      | sK1 != X1 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_414,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ v5_orders_2(sK1)
% 1.35/0.98      | ~ v3_orders_2(sK1)
% 1.35/0.98      | ~ l1_orders_2(sK1)
% 1.35/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_413]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_27,negated_conjecture,
% 1.35/0.98      ( v3_orders_2(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_26,negated_conjecture,
% 1.35/0.98      ( v5_orders_2(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_23,negated_conjecture,
% 1.35/0.98      ( l1_waybel_9(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_16,plain,
% 1.35/0.98      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_52,plain,
% 1.35/0.98      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_418,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_414,c_27,c_26,c_23,c_52]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1384,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),k6_domain_1(u1_struct_0(sK1),X0_57)) = k6_waybel_0(sK1,X0_57) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_418]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1723,plain,
% 1.35/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),k6_domain_1(u1_struct_0(sK1),X0_57)) = k6_waybel_0(sK1,X0_57)
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1944,plain,
% 1.35/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
% 1.35/0.98      inference(superposition,[status(thm)],[c_1720,c_1723]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_5,plain,
% 1.35/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.35/0.98      | ~ v5_pre_topc(X0,X1,X2)
% 1.35/0.98      | ~ v4_pre_topc(X3,X2)
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.35/0.98      | ~ l1_pre_topc(X2)
% 1.35/0.98      | ~ l1_pre_topc(X1)
% 1.35/0.98      | ~ v1_funct_1(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_14,plain,
% 1.35/0.98      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_359,plain,
% 1.35/0.98      ( l1_orders_2(X0) | sK1 != X0 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_360,plain,
% 1.35/0.98      ( l1_orders_2(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_359]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_666,plain,
% 1.35/0.98      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | sK1 != X0 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_360]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_667,plain,
% 1.35/0.98      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | v2_struct_0(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_666]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_25,negated_conjecture,
% 1.35/0.98      ( v1_lattice3(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_10,plain,
% 1.35/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_70,plain,
% 1.35/0.98      ( ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) | ~ l1_orders_2(sK1) ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_671,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_667,c_25,c_23,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_672,plain,
% 1.35/0.98      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_671]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_729,plain,
% 1.35/0.98      ( ~ v5_pre_topc(X0,X1,X2)
% 1.35/0.98      | ~ v4_pre_topc(X3,X2)
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.35/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.35/0.98      | ~ l1_pre_topc(X1)
% 1.35/0.98      | ~ l1_pre_topc(X2)
% 1.35/0.98      | ~ v1_funct_1(X0)
% 1.35/0.98      | k4_waybel_1(sK1,X4) != X0
% 1.35/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_672]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_730,plain,
% 1.35/0.98      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.35/0.98      | ~ v4_pre_topc(X3,X2)
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.35/0.98      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.35/0.98      | ~ l1_pre_topc(X1)
% 1.35/0.98      | ~ l1_pre_topc(X2)
% 1.35/0.98      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 1.35/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_729]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_15,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | v2_struct_0(X1)
% 1.35/0.98      | ~ l1_orders_2(X1)
% 1.35/0.98      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 1.35/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_684,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | v2_struct_0(X1)
% 1.35/0.98      | v1_funct_1(k4_waybel_1(X1,X0))
% 1.35/0.98      | sK1 != X1 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_360]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_685,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | v2_struct_0(sK1)
% 1.35/0.98      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_684]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_734,plain,
% 1.35/0.98      ( ~ l1_pre_topc(X2)
% 1.35/0.98      | ~ l1_pre_topc(X1)
% 1.35/0.98      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.35/0.98      | ~ v4_pre_topc(X3,X2)
% 1.35/0.98      | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.35/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_730,c_25,c_23,c_52,c_70,c_685]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_735,plain,
% 1.35/0.98      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.35/0.98      | ~ v4_pre_topc(X3,X2)
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.35/0.98      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.35/0.98      | ~ l1_pre_topc(X1)
% 1.35/0.98      | ~ l1_pre_topc(X2)
% 1.35/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_734]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1381,plain,
% 1.35/0.98      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_57),X0_58,X1_58)
% 1.35/0.98      | ~ v4_pre_topc(X1_57,X1_58)
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_58),u1_struct_0(X1_58),k4_waybel_1(sK1,X0_57),X1_57),X0_58)
% 1.35/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X1_58)))
% 1.35/0.98      | ~ m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58))))
% 1.35/0.98      | ~ l1_pre_topc(X1_58)
% 1.35/0.98      | ~ l1_pre_topc(X0_58)
% 1.35/0.98      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X0_58) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_735]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1728,plain,
% 1.35/0.98      ( u1_struct_0(X0_58) != u1_struct_0(sK1)
% 1.35/0.98      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 1.35/0.98      | v5_pre_topc(k4_waybel_1(sK1,X0_57),X1_58,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(X1_57,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(X1_58),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),X1_58) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 1.35/0.98      | l1_pre_topc(X1_58) != iProver_top
% 1.35/0.98      | l1_pre_topc(X0_58) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2351,plain,
% 1.35/0.98      ( u1_struct_0(X0_58) != u1_struct_0(sK1)
% 1.35/0.98      | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(X1_57,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 1.35/0.98      | l1_pre_topc(X0_58) != iProver_top
% 1.35/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 1.35/0.98      inference(equality_resolution,[status(thm)],[c_1728]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_36,plain,
% 1.35/0.98      ( l1_waybel_9(sK1) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_17,plain,
% 1.35/0.98      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_48,plain,
% 1.35/0.98      ( l1_waybel_9(X0) != iProver_top | l1_pre_topc(X0) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_50,plain,
% 1.35/0.98      ( l1_waybel_9(sK1) != iProver_top
% 1.35/0.98      | l1_pre_topc(sK1) = iProver_top ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_48]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2479,plain,
% 1.35/0.98      ( l1_pre_topc(X0_58) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
% 1.35/0.98      | v4_pre_topc(X1_57,X0_58) != iProver_top
% 1.35/0.98      | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
% 1.35/0.98      | u1_struct_0(X0_58) != u1_struct_0(sK1) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_2351,c_36,c_50]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2480,plain,
% 1.35/0.98      ( u1_struct_0(X0_58) != u1_struct_0(sK1)
% 1.35/0.98      | v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(X1_57,X0_58) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_58),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_58)))) != iProver_top
% 1.35/0.98      | l1_pre_topc(X0_58) != iProver_top ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_2479]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2491,plain,
% 1.35/0.98      ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1) != iProver_top
% 1.35/0.98      | v4_pre_topc(X1_57,sK1) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 1.35/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 1.35/0.98      inference(equality_resolution,[status(thm)],[c_2480]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_21,negated_conjecture,
% 1.35/0.98      ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1388,negated_conjecture,
% 1.35/0.98      ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1)
% 1.35/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1428,plain,
% 1.35/0.98      ( v5_pre_topc(k4_waybel_1(sK1,X0_57),sK1,sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_13,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.35/0.98      | v2_struct_0(X1)
% 1.35/0.98      | ~ l1_orders_2(X1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_702,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.35/0.98      | v2_struct_0(X1)
% 1.35/0.98      | sK1 != X1 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_360]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_703,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.35/0.98      | v2_struct_0(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_702]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_707,plain,
% 1.35/0.98      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_703,c_25,c_23,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_708,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_707]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1382,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_708]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1446,plain,
% 1.35/0.98      ( m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(k4_waybel_1(sK1,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2579,plain,
% 1.35/0.98      ( v4_pre_topc(X1_57,sK1) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_57),X1_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_2491,c_36,c_50,c_1428,c_1446]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2580,plain,
% 1.35/0.98      ( v4_pre_topc(X0_57,sK1) != iProver_top
% 1.35/0.98      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_57),X0_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X1_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_2579]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2589,plain,
% 1.35/0.98      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
% 1.35/0.98      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 1.35/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.35/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(superposition,[status(thm)],[c_1944,c_2580]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.35/0.98      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 1.35/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1391,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 1.35/0.98      | m1_subset_1(k8_relset_1(X0_59,X1_59,X0_57,X1_57),k1_zfmisc_1(X0_59)) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1716,plain,
% 1.35/0.98      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59))) != iProver_top
% 1.35/0.98      | m1_subset_1(k8_relset_1(X0_59,X1_59,X0_57,X1_57),k1_zfmisc_1(X0_59)) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_2039,plain,
% 1.35/0.98      ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 1.35/0.98      | m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.35/0.98      inference(superposition,[status(thm)],[c_1944,c_1716]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_0,plain,
% 1.35/0.98      ( ~ r2_hidden(X0,X1)
% 1.35/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.35/0.98      | ~ v1_xboole_0(X2) ),
% 1.35/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_11,plain,
% 1.35/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.35/0.98      | r2_hidden(X2,k6_waybel_0(X0,X1))
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_435,plain,
% 1.35/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0)
% 1.35/0.98      | ~ v1_xboole_0(X4)
% 1.35/0.98      | X2 != X5
% 1.35/0.98      | k6_waybel_0(X0,X1) != X3 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_436,plain,
% 1.35/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(X3))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0)
% 1.35/0.98      | ~ v1_xboole_0(X3) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_435]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_9,plain,
% 1.35/0.98      ( r3_orders_2(X0,X1,X1)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ v3_orders_2(X0)
% 1.35/0.98      | ~ l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_508,plain,
% 1.35/0.98      ( r3_orders_2(X0,X1,X1)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0)
% 1.35/0.98      | sK1 != X0 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_509,plain,
% 1.35/0.98      ( r3_orders_2(sK1,X0,X0)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.35/0.98      | v2_struct_0(sK1)
% 1.35/0.98      | ~ l1_orders_2(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_508]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_513,plain,
% 1.35/0.98      ( r3_orders_2(sK1,X0,X0)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_509,c_25,c_23,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_8,plain,
% 1.35/0.98      ( r1_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ r3_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ v3_orders_2(X0)
% 1.35/0.98      | ~ l1_orders_2(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_529,plain,
% 1.35/0.98      ( r1_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ r3_orders_2(X0,X1,X2)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_orders_2(X0)
% 1.35/0.98      | sK1 != X0 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_530,plain,
% 1.35/0.98      ( r1_orders_2(sK1,X0,X1)
% 1.35/0.98      | ~ r3_orders_2(sK1,X0,X1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.35/0.98      | v2_struct_0(sK1)
% 1.35/0.98      | ~ l1_orders_2(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_529]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_534,plain,
% 1.35/0.98      ( r1_orders_2(sK1,X0,X1)
% 1.35/0.98      | ~ r3_orders_2(sK1,X0,X1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_530,c_25,c_23,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_592,plain,
% 1.35/0.98      ( r1_orders_2(sK1,X0,X1)
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.35/0.98      | X0 != X2
% 1.35/0.98      | X1 != X2
% 1.35/0.98      | sK1 != sK1 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_513,c_534]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_593,plain,
% 1.35/0.98      ( r1_orders_2(sK1,X0,X0)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_592]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_611,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.35/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.35/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(X5))
% 1.35/0.98      | v2_struct_0(X1)
% 1.35/0.98      | ~ l1_orders_2(X1)
% 1.35/0.98      | ~ v1_xboole_0(X5)
% 1.35/0.98      | X3 != X2
% 1.35/0.98      | X3 != X0
% 1.35/0.98      | sK1 != X1 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_436,c_593]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_612,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(X2))
% 1.35/0.98      | v2_struct_0(sK1)
% 1.35/0.98      | ~ l1_orders_2(sK1)
% 1.35/0.98      | ~ v1_xboole_0(X2) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_611]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_616,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(X2))
% 1.35/0.98      | ~ v1_xboole_0(X2) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_612,c_25,c_23,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1383,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(X1_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
% 1.35/0.98      | ~ v1_xboole_0(X0_59) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_616]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1393,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
% 1.35/0.98      | ~ v1_xboole_0(X0_59)
% 1.35/0.98      | ~ sP1_iProver_split ),
% 1.35/0.98      inference(splitting,
% 1.35/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.35/0.98                [c_1383]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1394,plain,
% 1.35/0.98      ( sP1_iProver_split | sP0_iProver_split ),
% 1.35/0.98      inference(splitting,
% 1.35/0.98                [splitting(split),new_symbols(definition,[])],
% 1.35/0.98                [c_1383]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1392,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1)) | ~ sP0_iProver_split ),
% 1.35/0.98      inference(splitting,
% 1.35/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.35/0.98                [c_1383]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1444,plain,
% 1.35/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK1)) | ~ sP0_iProver_split ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1392]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1497,plain,
% 1.35/0.98      ( ~ v1_xboole_0(X0_59)
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
% 1.35/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_1393,c_22,c_1394,c_1444]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1498,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(X0_59))
% 1.35/0.98      | ~ v1_xboole_0(X0_59) ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_1497]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1929,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,u1_struct_0(sK1))
% 1.35/0.98      | ~ m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.35/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1498]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1930,plain,
% 1.35/0.98      ( m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | m1_subset_1(k6_waybel_0(sK1,X0_57),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.35/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1932,plain,
% 1.35/0.98      ( m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.35/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1930]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_6,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,X1)
% 1.35/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.35/0.98      | v1_xboole_0(X1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1390,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0_57,X0_59)
% 1.35/0.98      | m1_subset_1(k6_domain_1(X0_59,X0_57),k1_zfmisc_1(X0_59))
% 1.35/0.98      | v1_xboole_0(X0_59) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1885,plain,
% 1.35/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.35/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.35/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1390]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1886,plain,
% 1.35/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.35/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.35/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1448,plain,
% 1.35/0.98      ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 1.35/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1446]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_18,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | ~ v2_pre_topc(X0)
% 1.35/0.98      | ~ v8_pre_topc(X0)
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_pre_topc(X0) ),
% 1.35/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_28,negated_conjecture,
% 1.35/0.98      ( v8_pre_topc(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_392,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.35/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.35/0.98      | ~ v2_pre_topc(X0)
% 1.35/0.98      | v2_struct_0(X0)
% 1.35/0.98      | ~ l1_pre_topc(X0)
% 1.35/0.98      | sK1 != X0 ),
% 1.35/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_393,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | ~ v2_pre_topc(sK1)
% 1.35/0.98      | v2_struct_0(sK1)
% 1.35/0.98      | ~ l1_pre_topc(sK1) ),
% 1.35/0.98      inference(unflattening,[status(thm)],[c_392]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_29,negated_conjecture,
% 1.35/0.98      ( v2_pre_topc(sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_49,plain,
% 1.35/0.98      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_397,plain,
% 1.35/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.35/0.98      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
% 1.35/0.98      inference(global_propositional_subsumption,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_393,c_29,c_25,c_23,c_49,c_52,c_70]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_398,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.35/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(renaming,[status(thm)],[c_397]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1385,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_57),sK1)
% 1.35/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
% 1.35/0.98      inference(subtyping,[status(esa)],[c_398]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1433,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_57),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(X0_57,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_1435,plain,
% 1.35/0.98      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 1.35/0.98      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.35/0.98      inference(instantiation,[status(thm)],[c_1433]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_20,negated_conjecture,
% 1.35/0.98      ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
% 1.35/0.98      inference(cnf_transformation,[],[f77]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_41,plain,
% 1.35/0.98      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(c_37,plain,
% 1.35/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.35/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.35/0.98  
% 1.35/0.98  cnf(contradiction,plain,
% 1.35/0.98      ( $false ),
% 1.35/0.98      inference(minisat,
% 1.35/0.98                [status(thm)],
% 1.35/0.98                [c_2589,c_2039,c_1932,c_1886,c_1448,c_1435,c_41,c_37]) ).
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.35/0.98  
% 1.35/0.98  ------                               Statistics
% 1.35/0.98  
% 1.35/0.98  ------ General
% 1.35/0.98  
% 1.35/0.98  abstr_ref_over_cycles:                  0
% 1.35/0.98  abstr_ref_under_cycles:                 0
% 1.35/0.98  gc_basic_clause_elim:                   0
% 1.35/0.98  forced_gc_time:                         0
% 1.35/0.98  parsing_time:                           0.01
% 1.35/0.98  unif_index_cands_time:                  0.
% 1.35/0.98  unif_index_add_time:                    0.
% 1.35/0.98  orderings_time:                         0.
% 1.35/0.98  out_proof_time:                         0.01
% 1.35/0.98  total_time:                             0.137
% 1.35/0.98  num_of_symbols:                         65
% 1.35/0.98  num_of_terms:                           2405
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing
% 1.35/0.98  
% 1.35/0.98  num_of_splits:                          2
% 1.35/0.98  num_of_split_atoms:                     2
% 1.35/0.98  num_of_reused_defs:                     0
% 1.35/0.98  num_eq_ax_congr_red:                    33
% 1.35/0.98  num_of_sem_filtered_clauses:            3
% 1.35/0.98  num_of_subtypes:                        3
% 1.35/0.98  monotx_restored_types:                  0
% 1.35/0.98  sat_num_of_epr_types:                   0
% 1.35/0.98  sat_num_of_non_cyclic_types:            0
% 1.35/0.98  sat_guarded_non_collapsed_types:        0
% 1.35/0.98  num_pure_diseq_elim:                    0
% 1.35/0.98  simp_replaced_by:                       0
% 1.35/0.98  res_preprocessed:                       101
% 1.35/0.98  prep_upred:                             0
% 1.35/0.98  prep_unflattend:                        30
% 1.35/0.98  smt_new_axioms:                         0
% 1.35/0.98  pred_elim_cands:                        5
% 1.35/0.98  pred_elim:                              14
% 1.35/0.98  pred_elim_cl:                           16
% 1.35/0.98  pred_elim_cycles:                       20
% 1.35/0.98  merged_defs:                            0
% 1.35/0.98  merged_defs_ncl:                        0
% 1.35/0.98  bin_hyper_res:                          0
% 1.35/0.98  prep_cycles:                            4
% 1.35/0.98  pred_elim_time:                         0.038
% 1.35/0.98  splitting_time:                         0.
% 1.35/0.98  sem_filter_time:                        0.
% 1.35/0.98  monotx_time:                            0.
% 1.35/0.98  subtype_inf_time:                       0.
% 1.35/0.98  
% 1.35/0.98  ------ Problem properties
% 1.35/0.98  
% 1.35/0.98  clauses:                                16
% 1.35/0.98  conjectures:                            3
% 1.35/0.98  epr:                                    2
% 1.35/0.98  horn:                                   12
% 1.35/0.98  ground:                                 4
% 1.35/0.98  unary:                                  3
% 1.35/0.98  binary:                                 7
% 1.35/0.98  lits:                                   58
% 1.35/0.98  lits_eq:                                9
% 1.35/0.98  fd_pure:                                0
% 1.35/0.98  fd_pseudo:                              0
% 1.35/0.98  fd_cond:                                0
% 1.35/0.98  fd_pseudo_cond:                         0
% 1.35/0.98  ac_symbols:                             0
% 1.35/0.98  
% 1.35/0.98  ------ Propositional Solver
% 1.35/0.98  
% 1.35/0.98  prop_solver_calls:                      26
% 1.35/0.98  prop_fast_solver_calls:                 1100
% 1.35/0.98  smt_solver_calls:                       0
% 1.35/0.98  smt_fast_solver_calls:                  0
% 1.35/0.98  prop_num_of_clauses:                    626
% 1.35/0.98  prop_preprocess_simplified:             3290
% 1.35/0.98  prop_fo_subsumed:                       40
% 1.35/0.98  prop_solver_time:                       0.
% 1.35/0.98  smt_solver_time:                        0.
% 1.35/0.98  smt_fast_solver_time:                   0.
% 1.35/0.98  prop_fast_solver_time:                  0.
% 1.35/0.98  prop_unsat_core_time:                   0.
% 1.35/0.98  
% 1.35/0.98  ------ QBF
% 1.35/0.98  
% 1.35/0.98  qbf_q_res:                              0
% 1.35/0.98  qbf_num_tautologies:                    0
% 1.35/0.98  qbf_prep_cycles:                        0
% 1.35/0.98  
% 1.35/0.98  ------ BMC1
% 1.35/0.98  
% 1.35/0.98  bmc1_current_bound:                     -1
% 1.35/0.98  bmc1_last_solved_bound:                 -1
% 1.35/0.98  bmc1_unsat_core_size:                   -1
% 1.35/0.98  bmc1_unsat_core_parents_size:           -1
% 1.35/0.98  bmc1_merge_next_fun:                    0
% 1.35/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.35/0.98  
% 1.35/0.98  ------ Instantiation
% 1.35/0.98  
% 1.35/0.98  inst_num_of_clauses:                    147
% 1.35/0.98  inst_num_in_passive:                    3
% 1.35/0.98  inst_num_in_active:                     111
% 1.35/0.98  inst_num_in_unprocessed:                33
% 1.35/0.98  inst_num_of_loops:                      120
% 1.35/0.98  inst_num_of_learning_restarts:          0
% 1.35/0.98  inst_num_moves_active_passive:          6
% 1.35/0.98  inst_lit_activity:                      0
% 1.35/0.98  inst_lit_activity_moves:                0
% 1.35/0.98  inst_num_tautologies:                   0
% 1.35/0.98  inst_num_prop_implied:                  0
% 1.35/0.98  inst_num_existing_simplified:           0
% 1.35/0.98  inst_num_eq_res_simplified:             0
% 1.35/0.98  inst_num_child_elim:                    0
% 1.35/0.98  inst_num_of_dismatching_blockings:      29
% 1.35/0.98  inst_num_of_non_proper_insts:           131
% 1.35/0.98  inst_num_of_duplicates:                 0
% 1.35/0.98  inst_inst_num_from_inst_to_res:         0
% 1.35/0.98  inst_dismatching_checking_time:         0.
% 1.35/0.98  
% 1.35/0.98  ------ Resolution
% 1.35/0.98  
% 1.35/0.98  res_num_of_clauses:                     0
% 1.35/0.98  res_num_in_passive:                     0
% 1.35/0.98  res_num_in_active:                      0
% 1.35/0.98  res_num_of_loops:                       105
% 1.35/0.98  res_forward_subset_subsumed:            25
% 1.35/0.98  res_backward_subset_subsumed:           0
% 1.35/0.98  res_forward_subsumed:                   0
% 1.35/0.98  res_backward_subsumed:                  0
% 1.35/0.98  res_forward_subsumption_resolution:     1
% 1.35/0.98  res_backward_subsumption_resolution:    0
% 1.35/0.98  res_clause_to_clause_subsumption:       56
% 1.35/0.98  res_orphan_elimination:                 0
% 1.35/0.98  res_tautology_del:                      48
% 1.35/0.98  res_num_eq_res_simplified:              0
% 1.35/0.98  res_num_sel_changes:                    0
% 1.35/0.98  res_moves_from_active_to_pass:          0
% 1.35/0.98  
% 1.35/0.98  ------ Superposition
% 1.35/0.98  
% 1.35/0.98  sup_time_total:                         0.
% 1.35/0.98  sup_time_generating:                    0.
% 1.35/0.98  sup_time_sim_full:                      0.
% 1.35/0.98  sup_time_sim_immed:                     0.
% 1.35/0.98  
% 1.35/0.98  sup_num_of_clauses:                     25
% 1.35/0.98  sup_num_in_active:                      24
% 1.35/0.98  sup_num_in_passive:                     1
% 1.35/0.98  sup_num_of_loops:                       23
% 1.35/0.98  sup_fw_superposition:                   4
% 1.35/0.98  sup_bw_superposition:                   0
% 1.35/0.98  sup_immediate_simplified:               3
% 1.35/0.98  sup_given_eliminated:                   0
% 1.35/0.98  comparisons_done:                       0
% 1.35/0.98  comparisons_avoided:                    0
% 1.35/0.98  
% 1.35/0.98  ------ Simplifications
% 1.35/0.98  
% 1.35/0.98  
% 1.35/0.98  sim_fw_subset_subsumed:                 1
% 1.35/0.98  sim_bw_subset_subsumed:                 0
% 1.35/0.98  sim_fw_subsumed:                        2
% 1.35/0.98  sim_bw_subsumed:                        0
% 1.35/0.98  sim_fw_subsumption_res:                 0
% 1.35/0.98  sim_bw_subsumption_res:                 0
% 1.35/0.98  sim_tautology_del:                      0
% 1.35/0.98  sim_eq_tautology_del:                   0
% 1.35/0.98  sim_eq_res_simp:                        0
% 1.35/0.98  sim_fw_demodulated:                     0
% 1.35/0.98  sim_bw_demodulated:                     0
% 1.35/0.98  sim_light_normalised:                   0
% 1.35/0.98  sim_joinable_taut:                      0
% 1.35/0.98  sim_joinable_simp:                      0
% 1.35/0.98  sim_ac_normalised:                      0
% 1.35/0.98  sim_smt_subsumption:                    0
% 1.35/0.98  
%------------------------------------------------------------------------------
