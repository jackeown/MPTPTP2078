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
% DateTime   : Thu Dec  3 12:28:55 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 659 expanded)
%              Number of clauses        :  101 ( 190 expanded)
%              Number of leaves         :   16 ( 149 expanded)
%              Depth                    :   28
%              Number of atoms          :  710 (4627 expanded)
%              Number of equality atoms :  126 ( 138 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_waybel_0(X0,X1),X0)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_pre_topc(k6_waybel_0(X0,sK3),X0)
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
          ( ~ v4_pre_topc(k6_waybel_0(sK2,X1),sK2)
          & ! [X2] :
              ( v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2)
              | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_waybel_9(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2)
      & v8_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ v4_pre_topc(k6_waybel_0(sK2,sK3),sK2)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_waybel_9(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2)
    & v8_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f44,f43])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    l1_waybel_9(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

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
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
        & v4_pre_topc(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0)
                    & v4_pre_topc(sK1(X0,X1,X2),X1)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

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

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1161,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1472,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0),k6_domain_1(u1_struct_0(sK2),X0)) = k6_waybel_0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_9(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_50,plain,
    ( ~ l1_waybel_9(sK2)
    | l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0),k6_domain_1(u1_struct_0(sK2),X0)) = k6_waybel_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_25,c_24,c_21,c_50])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),k6_domain_1(u1_struct_0(sK2),X0_56)) = k6_waybel_0(sK2,X0_56) ),
    inference(subtyping,[status(esa)],[c_419])).

cnf(c_1477,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),k6_domain_1(u1_struct_0(sK2),X0_56)) = k6_waybel_0(sK2,X0_56)
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_1781,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,sK3),k6_domain_1(u1_struct_0(sK2),sK3)) = k6_waybel_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1472,c_1477])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_318,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_319,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_65,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_321,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_23,c_21,c_50,c_65])).

cnf(c_435,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_321])).

cnf(c_436,plain,
    ( v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_21,c_50])).

cnf(c_441,plain,
    ( v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_519,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k4_waybel_1(sK2,X4) != X0
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_441])).

cnf(c_520,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(k4_waybel_1(sK2,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_321])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v1_funct_1(k4_waybel_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_524,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
    | ~ v4_pre_topc(X3,X2)
    | ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_21,c_50,c_454])).

cnf(c_525,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_1153,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK2,X0_56),X0_57,X1_57)
    | ~ v4_pre_topc(X1_56,X1_57)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),k4_waybel_1(sK2,X0_56),X1_56),X0_57)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_57)))
    | ~ m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | u1_struct_0(X1_57) != u1_struct_0(sK2)
    | u1_struct_0(X0_57) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_1480,plain,
    ( u1_struct_0(X0_57) != u1_struct_0(sK2)
    | u1_struct_0(X1_57) != u1_struct_0(sK2)
    | v5_pre_topc(k4_waybel_1(sK2,X0_56),X1_57,X0_57) != iProver_top
    | v4_pre_topc(X1_56,X0_57) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),X1_57) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_2110,plain,
    ( u1_struct_0(X0_57) != u1_struct_0(sK2)
    | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
    | v4_pre_topc(X1_56,X0_57) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1480])).

cnf(c_34,plain,
    ( l1_waybel_9(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_46,plain,
    ( l1_waybel_9(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_48,plain,
    ( l1_waybel_9(sK2) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_2384,plain,
    ( l1_pre_topc(X0_57) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
    | v4_pre_topc(X1_56,X0_57) != iProver_top
    | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
    | u1_struct_0(X0_57) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_34,c_48])).

cnf(c_2385,plain,
    ( u1_struct_0(X0_57) != u1_struct_0(sK2)
    | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
    | v4_pre_topc(X1_56,X0_57) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_2384])).

cnf(c_2396,plain,
    ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2) != iProver_top
    | v4_pre_topc(X1_56,sK2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2385])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK2,X0),sK2,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1162,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1192,plain,
    ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_321])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_476,plain,
    ( m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_21,c_50])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_1155,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1207,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_2470,plain,
    ( v4_pre_topc(X1_56,sK2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_34,c_48,c_1192,c_1207])).

cnf(c_2471,plain,
    ( v4_pre_topc(X0_56,sK2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X1_56),X0_56),sK2) = iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_2480,plain,
    ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) = iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK2),sK3),sK2) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_2471])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_321])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_494,plain,
    ( m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_21,c_50])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_1154,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
    | m1_subset_1(k6_waybel_0(sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_1479,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_waybel_0(sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_1474,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_xboole_0(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1879,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK2,X0_56)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1474])).

cnf(c_1896,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_3,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_389,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_390,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_47,plain,
    ( ~ l1_waybel_9(sK2)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_21,c_47])).

cnf(c_395,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1157,plain,
    ( v4_pre_topc(X0_56,sK2)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_395])).

cnf(c_1476,plain,
    ( v4_pre_topc(X0_56,sK2) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_1878,plain,
    ( v4_pre_topc(k6_waybel_0(sK2,X0_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK2,X0_56)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1476])).

cnf(c_1893,plain,
    ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | m1_subset_1(k6_domain_1(X1_56,X0_56),k1_zfmisc_1(X1_56))
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1633,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1634,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_16,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( v8_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_368,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_369,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27,c_23,c_21,c_47,c_50,c_65])).

cnf(c_374,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_1158,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0_56),sK2)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1198,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0_56),sK2) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_1200,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2480,c_1896,c_1893,c_1634,c_1200,c_39,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.65/1.00  
% 1.65/1.00  ------  iProver source info
% 1.65/1.00  
% 1.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.65/1.00  git: non_committed_changes: false
% 1.65/1.00  git: last_make_outside_of_git: false
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     num_symb
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       true
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  ------ Parsing...
% 1.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/1.00  ------ Proving...
% 1.65/1.00  ------ Problem Properties 
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  clauses                                 15
% 1.65/1.00  conjectures                             3
% 1.65/1.00  EPR                                     1
% 1.65/1.00  Horn                                    12
% 1.65/1.00  unary                                   3
% 1.65/1.00  binary                                  5
% 1.65/1.00  lits                                    56
% 1.65/1.00  lits eq                                 9
% 1.65/1.00  fd_pure                                 0
% 1.65/1.00  fd_pseudo                               0
% 1.65/1.00  fd_cond                                 0
% 1.65/1.00  fd_pseudo_cond                          0
% 1.65/1.00  AC symbols                              0
% 1.65/1.00  
% 1.65/1.00  ------ Schedule dynamic 5 is on 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  Current options:
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     none
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       false
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ Proving...
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS status Theorem for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  fof(f12,conjecture,(
% 1.65/1.00    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f13,negated_conjecture,(
% 1.65/1.00    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.65/1.00    inference(negated_conjecture,[],[f12])).
% 1.65/1.00  
% 1.65/1.00  fof(f14,plain,(
% 1.65/1.00    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.65/1.00    inference(pure_predicate_removal,[],[f13])).
% 1.65/1.00  
% 1.65/1.00  fof(f33,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f14])).
% 1.65/1.00  
% 1.65/1.00  fof(f34,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f33])).
% 1.65/1.00  
% 1.65/1.00  fof(f44,plain,(
% 1.65/1.00    ( ! [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k6_waybel_0(X0,sK3),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f43,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK2,X1),sK2) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_waybel_9(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & v8_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f45,plain,(
% 1.65/1.00    (~v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_waybel_9(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2) & v8_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f44,f43])).
% 1.65/1.00  
% 1.65/1.00  fof(f71,plain,(
% 1.65/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f11,axiom,(
% 1.65/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f31,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f11])).
% 1.65/1.00  
% 1.65/1.00  fof(f32,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.65/1.00    inference(flattening,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f63,plain,(
% 1.65/1.00    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f69,plain,(
% 1.65/1.00    v2_lattice3(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f66,plain,(
% 1.65/1.00    v3_orders_2(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f67,plain,(
% 1.65/1.00    v5_orders_2(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f70,plain,(
% 1.65/1.00    l1_waybel_9(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f9,axiom,(
% 1.65/1.00    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f28,plain,(
% 1.65/1.00    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f9])).
% 1.65/1.00  
% 1.65/1.00  fof(f61,plain,(
% 1.65/1.00    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f28])).
% 1.65/1.00  
% 1.65/1.00  fof(f4,axiom,(
% 1.65/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f18,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f4])).
% 1.65/1.00  
% 1.65/1.00  fof(f19,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f18])).
% 1.65/1.00  
% 1.65/1.00  fof(f39,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f19])).
% 1.65/1.00  
% 1.65/1.00  fof(f40,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(rectify,[],[f39])).
% 1.65/1.00  
% 1.65/1.00  fof(f41,plain,(
% 1.65/1.00    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v4_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f42,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)),X0) & v4_pre_topc(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 1.65/1.00  
% 1.65/1.00  fof(f50,plain,(
% 1.65/1.00    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f42])).
% 1.65/1.00  
% 1.65/1.00  fof(f8,axiom,(
% 1.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f26,plain,(
% 1.65/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f8])).
% 1.65/1.00  
% 1.65/1.00  fof(f27,plain,(
% 1.65/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f26])).
% 1.65/1.00  
% 1.65/1.00  fof(f58,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f27])).
% 1.65/1.00  
% 1.65/1.00  fof(f6,axiom,(
% 1.65/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f22,plain,(
% 1.65/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f6])).
% 1.65/1.00  
% 1.65/1.00  fof(f23,plain,(
% 1.65/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.65/1.00    inference(flattening,[],[f22])).
% 1.65/1.00  
% 1.65/1.00  fof(f55,plain,(
% 1.65/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f23])).
% 1.65/1.00  
% 1.65/1.00  fof(f68,plain,(
% 1.65/1.00    v1_lattice3(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f57,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f27])).
% 1.65/1.00  
% 1.65/1.00  fof(f60,plain,(
% 1.65/1.00    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f28])).
% 1.65/1.00  
% 1.65/1.00  fof(f72,plain,(
% 1.65/1.00    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK2,X2),sK2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK2))) )),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f59,plain,(
% 1.65/1.00    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f27])).
% 1.65/1.00  
% 1.65/1.00  fof(f7,axiom,(
% 1.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f24,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f7])).
% 1.65/1.00  
% 1.65/1.00  fof(f25,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f24])).
% 1.65/1.00  
% 1.65/1.00  fof(f56,plain,(
% 1.65/1.00    ( ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f25])).
% 1.65/1.00  
% 1.65/1.00  fof(f1,axiom,(
% 1.65/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f35,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(nnf_transformation,[],[f1])).
% 1.65/1.00  
% 1.65/1.00  fof(f36,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(rectify,[],[f35])).
% 1.65/1.00  
% 1.65/1.00  fof(f37,plain,(
% 1.65/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f38,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f47,plain,(
% 1.65/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f38])).
% 1.65/1.00  
% 1.65/1.00  fof(f2,axiom,(
% 1.65/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f15,plain,(
% 1.65/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.65/1.00    inference(ennf_transformation,[],[f2])).
% 1.65/1.00  
% 1.65/1.00  fof(f48,plain,(
% 1.65/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f15])).
% 1.65/1.00  
% 1.65/1.00  fof(f3,axiom,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f16,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f3])).
% 1.65/1.00  
% 1.65/1.00  fof(f17,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f16])).
% 1.65/1.00  
% 1.65/1.00  fof(f49,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f17])).
% 1.65/1.00  
% 1.65/1.00  fof(f64,plain,(
% 1.65/1.00    v2_pre_topc(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f5,axiom,(
% 1.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f20,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f5])).
% 1.65/1.00  
% 1.65/1.00  fof(f21,plain,(
% 1.65/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.65/1.00    inference(flattening,[],[f20])).
% 1.65/1.00  
% 1.65/1.00  fof(f54,plain,(
% 1.65/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f21])).
% 1.65/1.00  
% 1.65/1.00  fof(f10,axiom,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f29,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f10])).
% 1.65/1.00  
% 1.65/1.00  fof(f30,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f29])).
% 1.65/1.00  
% 1.65/1.00  fof(f62,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f30])).
% 1.65/1.00  
% 1.65/1.00  fof(f65,plain,(
% 1.65/1.00    v8_pre_topc(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  fof(f73,plain,(
% 1.65/1.00    ~v4_pre_topc(k6_waybel_0(sK2,sK3),sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f45])).
% 1.65/1.00  
% 1.65/1.00  cnf(c_20,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1161,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1472,plain,
% 1.65/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_17,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ v3_orders_2(X1)
% 1.65/1.00      | ~ v5_orders_2(X1)
% 1.65/1.00      | ~ v2_lattice3(X1)
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_22,negated_conjecture,
% 1.65/1.00      ( v2_lattice3(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_414,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ v3_orders_2(X1)
% 1.65/1.00      | ~ v5_orders_2(X1)
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_415,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | ~ v3_orders_2(sK2)
% 1.65/1.00      | ~ v5_orders_2(sK2)
% 1.65/1.00      | ~ l1_orders_2(sK2)
% 1.65/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0),k6_domain_1(u1_struct_0(sK2),X0)) = k6_waybel_0(sK2,X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_25,negated_conjecture,
% 1.65/1.00      ( v3_orders_2(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_24,negated_conjecture,
% 1.65/1.00      ( v5_orders_2(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_21,negated_conjecture,
% 1.65/1.00      ( l1_waybel_9(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_14,plain,
% 1.65/1.00      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_50,plain,
% 1.65/1.00      ( ~ l1_waybel_9(sK2) | l1_orders_2(sK2) ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_419,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0),k6_domain_1(u1_struct_0(sK2),X0)) = k6_waybel_0(sK2,X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_415,c_25,c_24,c_21,c_50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1156,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
% 1.65/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),k6_domain_1(u1_struct_0(sK2),X0_56)) = k6_waybel_0(sK2,X0_56) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_419]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1477,plain,
% 1.65/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),k6_domain_1(u1_struct_0(sK2),X0_56)) = k6_waybel_0(sK2,X0_56)
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1781,plain,
% 1.65/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,sK3),k6_domain_1(u1_struct_0(sK2),sK3)) = k6_waybel_0(sK2,sK3) ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1472,c_1477]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_7,plain,
% 1.65/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.65/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.65/1.00      | ~ v4_pre_topc(X3,X2)
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/1.00      | ~ v1_funct_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_12,plain,
% 1.65/1.00      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.65/1.00      | ~ l1_orders_2(X0)
% 1.65/1.00      | v2_struct_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_9,plain,
% 1.65/1.00      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_23,negated_conjecture,
% 1.65/1.00      ( v1_lattice3(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_318,plain,
% 1.65/1.00      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK2 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_319,plain,
% 1.65/1.00      ( ~ l1_orders_2(sK2) | ~ v2_struct_0(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_318]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_65,plain,
% 1.65/1.00      ( ~ l1_orders_2(sK2) | ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_321,plain,
% 1.65/1.00      ( ~ v2_struct_0(sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_319,c_23,c_21,c_50,c_65]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_435,plain,
% 1.65/1.00      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.65/1.00      | ~ l1_orders_2(X0)
% 1.65/1.00      | sK2 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_321]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_436,plain,
% 1.65/1.00      ( v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | ~ l1_orders_2(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_440,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_436,c_21,c_50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_441,plain,
% 1.65/1.00      ( v1_funct_2(k4_waybel_1(sK2,X0),u1_struct_0(sK2),u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_440]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_519,plain,
% 1.65/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 1.65/1.00      | ~ v4_pre_topc(X3,X2)
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.65/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/1.00      | ~ v1_funct_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X2)
% 1.65/1.00      | k4_waybel_1(sK2,X4) != X0
% 1.65/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_441]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_520,plain,
% 1.65/1.00      ( ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
% 1.65/1.00      | ~ v4_pre_topc(X3,X2)
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/1.00      | ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.65/1.00      | ~ v1_funct_1(k4_waybel_1(sK2,X0))
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X2)
% 1.65/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_519]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_13,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_453,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | v1_funct_1(k4_waybel_1(X1,X0))
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_321]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_454,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | ~ l1_orders_2(sK2)
% 1.65/1.00      | v1_funct_1(k4_waybel_1(sK2,X0)) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_524,plain,
% 1.65/1.00      ( ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
% 1.65/1.00      | ~ v4_pre_topc(X3,X2)
% 1.65/1.00      | ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X2)
% 1.65/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_520,c_21,c_50,c_454]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_525,plain,
% 1.65/1.00      ( ~ v5_pre_topc(k4_waybel_1(sK2,X0),X1,X2)
% 1.65/1.00      | ~ v4_pre_topc(X3,X2)
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK2,X0),X3),X1)
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/1.00      | ~ m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X2)
% 1.65/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X2) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_524]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1153,plain,
% 1.65/1.00      ( ~ v5_pre_topc(k4_waybel_1(sK2,X0_56),X0_57,X1_57)
% 1.65/1.00      | ~ v4_pre_topc(X1_56,X1_57)
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),k4_waybel_1(sK2,X0_56),X1_56),X0_57)
% 1.65/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK2))
% 1.65/1.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_57)))
% 1.65/1.00      | ~ m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 1.65/1.00      | ~ l1_pre_topc(X1_57)
% 1.65/1.00      | ~ l1_pre_topc(X0_57)
% 1.65/1.00      | u1_struct_0(X1_57) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X0_57) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_525]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1480,plain,
% 1.65/1.00      ( u1_struct_0(X0_57) != u1_struct_0(sK2)
% 1.65/1.00      | u1_struct_0(X1_57) != u1_struct_0(sK2)
% 1.65/1.00      | v5_pre_topc(k4_waybel_1(sK2,X0_56),X1_57,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(X1_56,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),X1_57) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
% 1.65/1.00      | l1_pre_topc(X1_57) != iProver_top
% 1.65/1.00      | l1_pre_topc(X0_57) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2110,plain,
% 1.65/1.00      ( u1_struct_0(X0_57) != u1_struct_0(sK2)
% 1.65/1.00      | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(X1_56,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
% 1.65/1.00      | l1_pre_topc(X0_57) != iProver_top
% 1.65/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 1.65/1.00      inference(equality_resolution,[status(thm)],[c_1480]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_34,plain,
% 1.65/1.00      ( l1_waybel_9(sK2) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_15,plain,
% 1.65/1.00      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_46,plain,
% 1.65/1.00      ( l1_waybel_9(X0) != iProver_top | l1_pre_topc(X0) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_48,plain,
% 1.65/1.00      ( l1_waybel_9(sK2) != iProver_top
% 1.65/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_46]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2384,plain,
% 1.65/1.00      ( l1_pre_topc(X0_57) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
% 1.65/1.00      | v4_pre_topc(X1_56,X0_57) != iProver_top
% 1.65/1.00      | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
% 1.65/1.00      | u1_struct_0(X0_57) != u1_struct_0(sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2110,c_34,c_48]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2385,plain,
% 1.65/1.00      ( u1_struct_0(X0_57) != u1_struct_0(sK2)
% 1.65/1.00      | v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(X1_56,X0_57) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
% 1.65/1.00      | l1_pre_topc(X0_57) != iProver_top ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_2384]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2396,plain,
% 1.65/1.00      ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2) != iProver_top
% 1.65/1.00      | v4_pre_topc(X1_56,sK2) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 1.65/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 1.65/1.00      inference(equality_resolution,[status(thm)],[c_2385]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_19,negated_conjecture,
% 1.65/1.00      ( v5_pre_topc(k4_waybel_1(sK2,X0),sK2,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1162,negated_conjecture,
% 1.65/1.00      ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1192,plain,
% 1.65/1.00      ( v5_pre_topc(k4_waybel_1(sK2,X0_56),sK2,sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1162]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_11,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | v2_struct_0(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_471,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_321]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_472,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.65/1.00      | ~ l1_orders_2(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_471]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_476,plain,
% 1.65/1.00      ( m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_472,c_21,c_50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_477,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_476]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1155,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_477]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1207,plain,
% 1.65/1.00      ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(k4_waybel_1(sK2,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2470,plain,
% 1.65/1.00      ( v4_pre_topc(X1_56,sK2) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X0_56),X1_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2396,c_34,c_48,c_1192,c_1207]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2471,plain,
% 1.65/1.00      ( v4_pre_topc(X0_56,sK2) != iProver_top
% 1.65/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k4_waybel_1(sK2,X1_56),X0_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X1_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_2470]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2480,plain,
% 1.65/1.00      ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) = iProver_top
% 1.65/1.00      | v4_pre_topc(k6_domain_1(u1_struct_0(sK2),sK3),sK2) != iProver_top
% 1.65/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1781,c_2471]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_10,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | v2_struct_0(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_489,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.65/1.00      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ l1_orders_2(X1)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_321]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_490,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ l1_orders_2(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_489]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_494,plain,
% 1.65/1.00      ( m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_490,c_21,c_50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_495,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k6_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_494]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1154,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0_56,u1_struct_0(sK2))
% 1.65/1.00      | m1_subset_1(k6_waybel_0(sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_495]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1479,plain,
% 1.65/1.00      ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | m1_subset_1(k6_waybel_0(sK2,X0_56),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_0,plain,
% 1.65/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.65/1.00      | ~ r2_hidden(X2,X0)
% 1.65/1.00      | ~ v1_xboole_0(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_351,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.65/1.00      | ~ v1_xboole_0(X1)
% 1.65/1.00      | v1_xboole_0(X2)
% 1.65/1.00      | X0 != X2
% 1.65/1.00      | sK0(X2) != X3 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_352,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.65/1.00      | ~ v1_xboole_0(X1)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_351]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1159,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 1.65/1.00      | ~ v1_xboole_0(X1_56)
% 1.65/1.00      | v1_xboole_0(X0_56) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_352]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1474,plain,
% 1.65/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 1.65/1.00      | v1_xboole_0(X1_56) != iProver_top
% 1.65/1.00      | v1_xboole_0(X0_56) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1879,plain,
% 1.65/1.00      ( m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v1_xboole_0(k6_waybel_0(sK2,X0_56)) = iProver_top
% 1.65/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1479,c_1474]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1896,plain,
% 1.65/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v1_xboole_0(k6_waybel_0(sK2,sK3)) = iProver_top
% 1.65/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_1879]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3,plain,
% 1.65/1.00      ( v4_pre_topc(X0,X1)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v1_xboole_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_27,negated_conjecture,
% 1.65/1.00      ( v2_pre_topc(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_389,plain,
% 1.65/1.00      ( v4_pre_topc(X0,X1)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v1_xboole_0(X0)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_390,plain,
% 1.65/1.00      ( v4_pre_topc(X0,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ l1_pre_topc(sK2)
% 1.65/1.00      | ~ v1_xboole_0(X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_47,plain,
% 1.65/1.00      ( ~ l1_waybel_9(sK2) | l1_pre_topc(sK2) ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_394,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v4_pre_topc(X0,sK2)
% 1.65/1.00      | ~ v1_xboole_0(X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_390,c_21,c_47]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_395,plain,
% 1.65/1.00      ( v4_pre_topc(X0,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v1_xboole_0(X0) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_394]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1157,plain,
% 1.65/1.00      ( v4_pre_topc(X0_56,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v1_xboole_0(X0_56) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_395]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1476,plain,
% 1.65/1.00      ( v4_pre_topc(X0_56,sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v1_xboole_0(X0_56) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1878,plain,
% 1.65/1.00      ( v4_pre_topc(k6_waybel_0(sK2,X0_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v1_xboole_0(k6_waybel_0(sK2,X0_56)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1479,c_1476]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1893,plain,
% 1.65/1.00      ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v1_xboole_0(k6_waybel_0(sK2,sK3)) != iProver_top ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_1878]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_8,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,X1)
% 1.65/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.65/1.00      | v1_xboole_0(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1164,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0_56,X1_56)
% 1.65/1.00      | m1_subset_1(k6_domain_1(X1_56,X0_56),k1_zfmisc_1(X1_56))
% 1.65/1.00      | v1_xboole_0(X1_56) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1633,plain,
% 1.65/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.65/1.00      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1634,plain,
% 1.65/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.65/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.65/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_16,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.65/1.00      | ~ v8_pre_topc(X0)
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | ~ v2_pre_topc(X0)
% 1.65/1.00      | ~ l1_pre_topc(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_26,negated_conjecture,
% 1.65/1.00      ( v8_pre_topc(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_368,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.65/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.65/1.00      | v2_struct_0(X0)
% 1.65/1.00      | ~ v2_pre_topc(X0)
% 1.65/1.00      | ~ l1_pre_topc(X0)
% 1.65/1.00      | sK2 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_369,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | v2_struct_0(sK2)
% 1.65/1.00      | ~ v2_pre_topc(sK2)
% 1.65/1.00      | ~ l1_pre_topc(sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_368]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_373,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.65/1.00      | v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_369,c_27,c_23,c_21,c_47,c_50,c_65]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_374,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_373]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1158,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0_56),sK2)
% 1.65/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(sK2)) ),
% 1.65/1.00      inference(subtyping,[status(esa)],[c_374]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1198,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),X0_56),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(X0_56,u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1200,plain,
% 1.65/1.00      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK2),sK3),sK2) = iProver_top
% 1.65/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_1198]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_18,negated_conjecture,
% 1.65/1.00      ( ~ v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_39,plain,
% 1.65/1.00      ( v4_pre_topc(k6_waybel_0(sK2,sK3),sK2) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_35,plain,
% 1.65/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(contradiction,plain,
% 1.65/1.00      ( $false ),
% 1.65/1.00      inference(minisat,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2480,c_1896,c_1893,c_1634,c_1200,c_39,c_35]) ).
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  ------                               Statistics
% 1.65/1.00  
% 1.65/1.00  ------ General
% 1.65/1.00  
% 1.65/1.00  abstr_ref_over_cycles:                  0
% 1.65/1.00  abstr_ref_under_cycles:                 0
% 1.65/1.00  gc_basic_clause_elim:                   0
% 1.65/1.00  forced_gc_time:                         0
% 1.65/1.00  parsing_time:                           0.012
% 1.65/1.00  unif_index_cands_time:                  0.
% 1.65/1.00  unif_index_add_time:                    0.
% 1.65/1.00  orderings_time:                         0.
% 1.65/1.00  out_proof_time:                         0.011
% 1.65/1.00  total_time:                             0.113
% 1.65/1.00  num_of_symbols:                         61
% 1.65/1.00  num_of_terms:                           2361
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing
% 1.65/1.00  
% 1.65/1.00  num_of_splits:                          0
% 1.65/1.00  num_of_split_atoms:                     0
% 1.65/1.00  num_of_reused_defs:                     0
% 1.65/1.00  num_eq_ax_congr_red:                    28
% 1.65/1.00  num_of_sem_filtered_clauses:            1
% 1.65/1.00  num_of_subtypes:                        2
% 1.65/1.00  monotx_restored_types:                  0
% 1.65/1.00  sat_num_of_epr_types:                   0
% 1.65/1.00  sat_num_of_non_cyclic_types:            0
% 1.65/1.00  sat_guarded_non_collapsed_types:        0
% 1.65/1.00  num_pure_diseq_elim:                    0
% 1.65/1.00  simp_replaced_by:                       0
% 1.65/1.00  res_preprocessed:                       96
% 1.65/1.00  prep_upred:                             0
% 1.65/1.00  prep_unflattend:                        22
% 1.65/1.00  smt_new_axioms:                         0
% 1.65/1.00  pred_elim_cands:                        5
% 1.65/1.00  pred_elim:                              12
% 1.65/1.00  pred_elim_cl:                           13
% 1.65/1.00  pred_elim_cycles:                       14
% 1.65/1.00  merged_defs:                            0
% 1.65/1.00  merged_defs_ncl:                        0
% 1.65/1.00  bin_hyper_res:                          0
% 1.65/1.00  prep_cycles:                            4
% 1.65/1.00  pred_elim_time:                         0.017
% 1.65/1.00  splitting_time:                         0.
% 1.65/1.00  sem_filter_time:                        0.
% 1.65/1.00  monotx_time:                            0.
% 1.65/1.00  subtype_inf_time:                       0.
% 1.65/1.00  
% 1.65/1.00  ------ Problem properties
% 1.65/1.00  
% 1.65/1.00  clauses:                                15
% 1.65/1.00  conjectures:                            3
% 1.65/1.00  epr:                                    1
% 1.65/1.00  horn:                                   12
% 1.65/1.00  ground:                                 3
% 1.65/1.00  unary:                                  3
% 1.65/1.00  binary:                                 5
% 1.65/1.00  lits:                                   56
% 1.65/1.00  lits_eq:                                9
% 1.65/1.00  fd_pure:                                0
% 1.65/1.00  fd_pseudo:                              0
% 1.65/1.00  fd_cond:                                0
% 1.65/1.00  fd_pseudo_cond:                         0
% 1.65/1.00  ac_symbols:                             0
% 1.65/1.00  
% 1.65/1.00  ------ Propositional Solver
% 1.65/1.00  
% 1.65/1.00  prop_solver_calls:                      26
% 1.65/1.00  prop_fast_solver_calls:                 991
% 1.65/1.00  smt_solver_calls:                       0
% 1.65/1.00  smt_fast_solver_calls:                  0
% 1.65/1.00  prop_num_of_clauses:                    631
% 1.65/1.00  prop_preprocess_simplified:             3267
% 1.65/1.00  prop_fo_subsumed:                       29
% 1.65/1.00  prop_solver_time:                       0.
% 1.65/1.00  smt_solver_time:                        0.
% 1.65/1.00  smt_fast_solver_time:                   0.
% 1.65/1.00  prop_fast_solver_time:                  0.
% 1.65/1.00  prop_unsat_core_time:                   0.
% 1.65/1.00  
% 1.65/1.00  ------ QBF
% 1.65/1.00  
% 1.65/1.00  qbf_q_res:                              0
% 1.65/1.00  qbf_num_tautologies:                    0
% 1.65/1.00  qbf_prep_cycles:                        0
% 1.65/1.00  
% 1.65/1.00  ------ BMC1
% 1.65/1.00  
% 1.65/1.00  bmc1_current_bound:                     -1
% 1.65/1.00  bmc1_last_solved_bound:                 -1
% 1.65/1.00  bmc1_unsat_core_size:                   -1
% 1.65/1.00  bmc1_unsat_core_parents_size:           -1
% 1.65/1.00  bmc1_merge_next_fun:                    0
% 1.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation
% 1.65/1.00  
% 1.65/1.00  inst_num_of_clauses:                    171
% 1.65/1.00  inst_num_in_passive:                    39
% 1.65/1.00  inst_num_in_active:                     122
% 1.65/1.00  inst_num_in_unprocessed:                10
% 1.65/1.00  inst_num_of_loops:                      130
% 1.65/1.00  inst_num_of_learning_restarts:          0
% 1.65/1.00  inst_num_moves_active_passive:          3
% 1.65/1.00  inst_lit_activity:                      0
% 1.65/1.00  inst_lit_activity_moves:                0
% 1.65/1.00  inst_num_tautologies:                   0
% 1.65/1.00  inst_num_prop_implied:                  0
% 1.65/1.00  inst_num_existing_simplified:           0
% 1.65/1.00  inst_num_eq_res_simplified:             0
% 1.65/1.00  inst_num_child_elim:                    0
% 1.65/1.00  inst_num_of_dismatching_blockings:      34
% 1.65/1.00  inst_num_of_non_proper_insts:           171
% 1.65/1.00  inst_num_of_duplicates:                 0
% 1.65/1.00  inst_inst_num_from_inst_to_res:         0
% 1.65/1.00  inst_dismatching_checking_time:         0.
% 1.65/1.00  
% 1.65/1.00  ------ Resolution
% 1.65/1.00  
% 1.65/1.00  res_num_of_clauses:                     0
% 1.65/1.00  res_num_in_passive:                     0
% 1.65/1.00  res_num_in_active:                      0
% 1.65/1.00  res_num_of_loops:                       100
% 1.65/1.00  res_forward_subset_subsumed:            35
% 1.65/1.00  res_backward_subset_subsumed:           2
% 1.65/1.00  res_forward_subsumed:                   0
% 1.65/1.00  res_backward_subsumed:                  0
% 1.65/1.00  res_forward_subsumption_resolution:     1
% 1.65/1.00  res_backward_subsumption_resolution:    0
% 1.65/1.00  res_clause_to_clause_subsumption:       35
% 1.65/1.00  res_orphan_elimination:                 0
% 1.65/1.00  res_tautology_del:                      47
% 1.65/1.00  res_num_eq_res_simplified:              0
% 1.65/1.00  res_num_sel_changes:                    0
% 1.65/1.00  res_moves_from_active_to_pass:          0
% 1.65/1.00  
% 1.65/1.00  ------ Superposition
% 1.65/1.00  
% 1.65/1.00  sup_time_total:                         0.
% 1.65/1.00  sup_time_generating:                    0.
% 1.65/1.00  sup_time_sim_full:                      0.
% 1.65/1.00  sup_time_sim_immed:                     0.
% 1.65/1.00  
% 1.65/1.00  sup_num_of_clauses:                     27
% 1.65/1.00  sup_num_in_active:                      25
% 1.65/1.00  sup_num_in_passive:                     2
% 1.65/1.00  sup_num_of_loops:                       24
% 1.65/1.00  sup_fw_superposition:                   3
% 1.65/1.00  sup_bw_superposition:                   5
% 1.65/1.00  sup_immediate_simplified:               4
% 1.65/1.00  sup_given_eliminated:                   0
% 1.65/1.00  comparisons_done:                       0
% 1.65/1.00  comparisons_avoided:                    0
% 1.65/1.00  
% 1.65/1.00  ------ Simplifications
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  sim_fw_subset_subsumed:                 2
% 1.65/1.00  sim_bw_subset_subsumed:                 0
% 1.65/1.00  sim_fw_subsumed:                        2
% 1.65/1.00  sim_bw_subsumed:                        0
% 1.65/1.00  sim_fw_subsumption_res:                 0
% 1.65/1.00  sim_bw_subsumption_res:                 0
% 1.65/1.00  sim_tautology_del:                      1
% 1.65/1.00  sim_eq_tautology_del:                   0
% 1.65/1.00  sim_eq_res_simp:                        0
% 1.65/1.00  sim_fw_demodulated:                     0
% 1.65/1.00  sim_bw_demodulated:                     0
% 1.65/1.00  sim_light_normalised:                   0
% 1.65/1.00  sim_joinable_taut:                      0
% 1.65/1.00  sim_joinable_simp:                      0
% 1.65/1.00  sim_ac_normalised:                      0
% 1.65/1.00  sim_smt_subsumption:                    0
% 1.65/1.00  
%------------------------------------------------------------------------------
