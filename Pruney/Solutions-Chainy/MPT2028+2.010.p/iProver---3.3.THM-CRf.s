%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:56 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 514 expanded)
%              Number of clauses        :   89 ( 146 expanded)
%              Number of leaves         :   13 ( 117 expanded)
%              Depth                    :   27
%              Number of atoms          :  613 (3610 expanded)
%              Number of equality atoms :  106 ( 113 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1110,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1376,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_47,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_22,c_21,c_18,c_47])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),k6_domain_1(u1_struct_0(sK1),X0_55)) = k6_waybel_0(sK1,X0_55) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_1379,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),k6_domain_1(u1_struct_0(sK1),X0_55)) = k6_waybel_0(sK1,X0_55)
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_1597,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1376,c_1379])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_304,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_305,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_433,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_305])).

cnf(c_434,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_20,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_59,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_20,c_18,c_47,c_59])).

cnf(c_439,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_488,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k4_waybel_1(sK1,X4) != X0
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_439])).

cnf(c_489,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_305])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_493,plain,
    ( ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ v4_pre_topc(X3,X2)
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_20,c_18,c_47,c_59,c_398])).

cnf(c_494,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_1104,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_55),X0_56,X1_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v4_pre_topc(X1_55,X1_56)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),k4_waybel_1(sK1,X0_55),X1_55),X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | u1_struct_0(X0_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1382,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_55),X1_56,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) != iProver_top
    | v4_pre_topc(X1_55,X0_56) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1_56),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),X1_56) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_1828,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
    | v4_pre_topc(X1_55,X0_56) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1382])).

cnf(c_31,plain,
    ( l1_waybel_9(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_43,plain,
    ( l1_waybel_9(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_45,plain,
    ( l1_waybel_9(sK1) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_1888,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
    | v4_pre_topc(X1_55,X0_56) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_31,c_45])).

cnf(c_1889,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
    | v4_pre_topc(X1_55,X0_56) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_1888])).

cnf(c_1900,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v4_pre_topc(X1_55,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1889])).

cnf(c_16,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1111,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1140,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_305])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_20,c_18,c_47,c_59])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_420])).

cnf(c_1106,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1151,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_1987,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
    | v4_pre_topc(X1_55,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1900,c_31,c_45,c_1140,c_1151])).

cnf(c_1988,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(X0_55,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_55),X0_55),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1987])).

cnf(c_1997,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1988])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_315,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_4,c_5])).

cnf(c_284,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_285,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_287,plain,
    ( ~ v2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_20,c_18,c_47,c_59])).

cnf(c_460,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_315,c_287])).

cnf(c_461,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_44,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_65,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_68,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_463,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_20,c_18,c_44,c_47,c_59,c_65,c_68])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_463])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_55),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_474])).

cnf(c_1154,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_1156,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_24,c_20,c_18,c_44,c_47,c_59])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_55),sK1) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_1145,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_55),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1147,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1997,c_1156,c_1147,c_36,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:16:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.21/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.21/0.99  
% 1.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.21/0.99  
% 1.21/0.99  ------  iProver source info
% 1.21/0.99  
% 1.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.21/0.99  git: non_committed_changes: false
% 1.21/0.99  git: last_make_outside_of_git: false
% 1.21/0.99  
% 1.21/0.99  ------ 
% 1.21/0.99  
% 1.21/0.99  ------ Input Options
% 1.21/0.99  
% 1.21/0.99  --out_options                           all
% 1.21/0.99  --tptp_safe_out                         true
% 1.21/0.99  --problem_path                          ""
% 1.21/0.99  --include_path                          ""
% 1.21/0.99  --clausifier                            res/vclausify_rel
% 1.21/0.99  --clausifier_options                    --mode clausify
% 1.21/0.99  --stdin                                 false
% 1.21/0.99  --stats_out                             all
% 1.21/0.99  
% 1.21/0.99  ------ General Options
% 1.21/0.99  
% 1.21/0.99  --fof                                   false
% 1.21/0.99  --time_out_real                         305.
% 1.21/0.99  --time_out_virtual                      -1.
% 1.21/0.99  --symbol_type_check                     false
% 1.21/0.99  --clausify_out                          false
% 1.21/0.99  --sig_cnt_out                           false
% 1.21/0.99  --trig_cnt_out                          false
% 1.21/0.99  --trig_cnt_out_tolerance                1.
% 1.21/0.99  --trig_cnt_out_sk_spl                   false
% 1.21/0.99  --abstr_cl_out                          false
% 1.21/0.99  
% 1.21/0.99  ------ Global Options
% 1.21/0.99  
% 1.21/0.99  --schedule                              default
% 1.21/0.99  --add_important_lit                     false
% 1.21/0.99  --prop_solver_per_cl                    1000
% 1.21/0.99  --min_unsat_core                        false
% 1.21/0.99  --soft_assumptions                      false
% 1.21/0.99  --soft_lemma_size                       3
% 1.21/0.99  --prop_impl_unit_size                   0
% 1.21/0.99  --prop_impl_unit                        []
% 1.21/0.99  --share_sel_clauses                     true
% 1.21/0.99  --reset_solvers                         false
% 1.21/0.99  --bc_imp_inh                            [conj_cone]
% 1.21/0.99  --conj_cone_tolerance                   3.
% 1.21/0.99  --extra_neg_conj                        none
% 1.21/0.99  --large_theory_mode                     true
% 1.21/0.99  --prolific_symb_bound                   200
% 1.21/0.99  --lt_threshold                          2000
% 1.21/0.99  --clause_weak_htbl                      true
% 1.21/0.99  --gc_record_bc_elim                     false
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing Options
% 1.21/0.99  
% 1.21/0.99  --preprocessing_flag                    true
% 1.21/0.99  --time_out_prep_mult                    0.1
% 1.21/0.99  --splitting_mode                        input
% 1.21/0.99  --splitting_grd                         true
% 1.21/0.99  --splitting_cvd                         false
% 1.21/0.99  --splitting_cvd_svl                     false
% 1.21/0.99  --splitting_nvd                         32
% 1.21/0.99  --sub_typing                            true
% 1.21/0.99  --prep_gs_sim                           true
% 1.21/0.99  --prep_unflatten                        true
% 1.21/0.99  --prep_res_sim                          true
% 1.21/0.99  --prep_upred                            true
% 1.21/0.99  --prep_sem_filter                       exhaustive
% 1.21/0.99  --prep_sem_filter_out                   false
% 1.21/0.99  --pred_elim                             true
% 1.21/0.99  --res_sim_input                         true
% 1.21/0.99  --eq_ax_congr_red                       true
% 1.21/0.99  --pure_diseq_elim                       true
% 1.21/0.99  --brand_transform                       false
% 1.21/0.99  --non_eq_to_eq                          false
% 1.21/0.99  --prep_def_merge                        true
% 1.21/0.99  --prep_def_merge_prop_impl              false
% 1.21/0.99  --prep_def_merge_mbd                    true
% 1.21/0.99  --prep_def_merge_tr_red                 false
% 1.21/0.99  --prep_def_merge_tr_cl                  false
% 1.21/0.99  --smt_preprocessing                     true
% 1.21/0.99  --smt_ac_axioms                         fast
% 1.21/0.99  --preprocessed_out                      false
% 1.21/0.99  --preprocessed_stats                    false
% 1.21/0.99  
% 1.21/0.99  ------ Abstraction refinement Options
% 1.21/0.99  
% 1.21/0.99  --abstr_ref                             []
% 1.21/0.99  --abstr_ref_prep                        false
% 1.21/0.99  --abstr_ref_until_sat                   false
% 1.21/0.99  --abstr_ref_sig_restrict                funpre
% 1.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/0.99  --abstr_ref_under                       []
% 1.21/0.99  
% 1.21/0.99  ------ SAT Options
% 1.21/0.99  
% 1.21/0.99  --sat_mode                              false
% 1.21/0.99  --sat_fm_restart_options                ""
% 1.21/0.99  --sat_gr_def                            false
% 1.21/0.99  --sat_epr_types                         true
% 1.21/0.99  --sat_non_cyclic_types                  false
% 1.21/0.99  --sat_finite_models                     false
% 1.21/0.99  --sat_fm_lemmas                         false
% 1.21/0.99  --sat_fm_prep                           false
% 1.21/0.99  --sat_fm_uc_incr                        true
% 1.21/0.99  --sat_out_model                         small
% 1.21/0.99  --sat_out_clauses                       false
% 1.21/0.99  
% 1.21/0.99  ------ QBF Options
% 1.21/0.99  
% 1.21/0.99  --qbf_mode                              false
% 1.21/0.99  --qbf_elim_univ                         false
% 1.21/0.99  --qbf_dom_inst                          none
% 1.21/0.99  --qbf_dom_pre_inst                      false
% 1.21/0.99  --qbf_sk_in                             false
% 1.21/0.99  --qbf_pred_elim                         true
% 1.21/0.99  --qbf_split                             512
% 1.21/0.99  
% 1.21/0.99  ------ BMC1 Options
% 1.21/0.99  
% 1.21/0.99  --bmc1_incremental                      false
% 1.21/0.99  --bmc1_axioms                           reachable_all
% 1.21/0.99  --bmc1_min_bound                        0
% 1.21/0.99  --bmc1_max_bound                        -1
% 1.21/0.99  --bmc1_max_bound_default                -1
% 1.21/0.99  --bmc1_symbol_reachability              true
% 1.21/0.99  --bmc1_property_lemmas                  false
% 1.21/0.99  --bmc1_k_induction                      false
% 1.21/0.99  --bmc1_non_equiv_states                 false
% 1.21/0.99  --bmc1_deadlock                         false
% 1.21/0.99  --bmc1_ucm                              false
% 1.21/0.99  --bmc1_add_unsat_core                   none
% 1.21/0.99  --bmc1_unsat_core_children              false
% 1.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/0.99  --bmc1_out_stat                         full
% 1.21/0.99  --bmc1_ground_init                      false
% 1.21/0.99  --bmc1_pre_inst_next_state              false
% 1.21/0.99  --bmc1_pre_inst_state                   false
% 1.21/0.99  --bmc1_pre_inst_reach_state             false
% 1.21/0.99  --bmc1_out_unsat_core                   false
% 1.21/0.99  --bmc1_aig_witness_out                  false
% 1.21/0.99  --bmc1_verbose                          false
% 1.21/0.99  --bmc1_dump_clauses_tptp                false
% 1.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.21/0.99  --bmc1_dump_file                        -
% 1.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.21/0.99  --bmc1_ucm_extend_mode                  1
% 1.21/0.99  --bmc1_ucm_init_mode                    2
% 1.21/0.99  --bmc1_ucm_cone_mode                    none
% 1.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.21/0.99  --bmc1_ucm_relax_model                  4
% 1.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/0.99  --bmc1_ucm_layered_model                none
% 1.21/0.99  --bmc1_ucm_max_lemma_size               10
% 1.21/0.99  
% 1.21/0.99  ------ AIG Options
% 1.21/0.99  
% 1.21/0.99  --aig_mode                              false
% 1.21/0.99  
% 1.21/0.99  ------ Instantiation Options
% 1.21/0.99  
% 1.21/0.99  --instantiation_flag                    true
% 1.21/0.99  --inst_sos_flag                         false
% 1.21/0.99  --inst_sos_phase                        true
% 1.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/0.99  --inst_lit_sel_side                     num_symb
% 1.21/0.99  --inst_solver_per_active                1400
% 1.21/0.99  --inst_solver_calls_frac                1.
% 1.21/0.99  --inst_passive_queue_type               priority_queues
% 1.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/0.99  --inst_passive_queues_freq              [25;2]
% 1.21/0.99  --inst_dismatching                      true
% 1.21/0.99  --inst_eager_unprocessed_to_passive     true
% 1.21/0.99  --inst_prop_sim_given                   true
% 1.21/0.99  --inst_prop_sim_new                     false
% 1.21/0.99  --inst_subs_new                         false
% 1.21/0.99  --inst_eq_res_simp                      false
% 1.21/0.99  --inst_subs_given                       false
% 1.21/0.99  --inst_orphan_elimination               true
% 1.21/0.99  --inst_learning_loop_flag               true
% 1.21/0.99  --inst_learning_start                   3000
% 1.21/0.99  --inst_learning_factor                  2
% 1.21/0.99  --inst_start_prop_sim_after_learn       3
% 1.21/0.99  --inst_sel_renew                        solver
% 1.21/0.99  --inst_lit_activity_flag                true
% 1.21/0.99  --inst_restr_to_given                   false
% 1.21/0.99  --inst_activity_threshold               500
% 1.21/0.99  --inst_out_proof                        true
% 1.21/0.99  
% 1.21/0.99  ------ Resolution Options
% 1.21/0.99  
% 1.21/0.99  --resolution_flag                       true
% 1.21/0.99  --res_lit_sel                           adaptive
% 1.21/0.99  --res_lit_sel_side                      none
% 1.21/0.99  --res_ordering                          kbo
% 1.21/0.99  --res_to_prop_solver                    active
% 1.21/0.99  --res_prop_simpl_new                    false
% 1.21/0.99  --res_prop_simpl_given                  true
% 1.21/0.99  --res_passive_queue_type                priority_queues
% 1.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/0.99  --res_passive_queues_freq               [15;5]
% 1.21/0.99  --res_forward_subs                      full
% 1.21/0.99  --res_backward_subs                     full
% 1.21/0.99  --res_forward_subs_resolution           true
% 1.21/0.99  --res_backward_subs_resolution          true
% 1.21/0.99  --res_orphan_elimination                true
% 1.21/0.99  --res_time_limit                        2.
% 1.21/0.99  --res_out_proof                         true
% 1.21/0.99  
% 1.21/0.99  ------ Superposition Options
% 1.21/0.99  
% 1.21/0.99  --superposition_flag                    true
% 1.21/0.99  --sup_passive_queue_type                priority_queues
% 1.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.21/0.99  --demod_completeness_check              fast
% 1.21/0.99  --demod_use_ground                      true
% 1.21/0.99  --sup_to_prop_solver                    passive
% 1.21/0.99  --sup_prop_simpl_new                    true
% 1.21/0.99  --sup_prop_simpl_given                  true
% 1.21/0.99  --sup_fun_splitting                     false
% 1.21/0.99  --sup_smt_interval                      50000
% 1.21/0.99  
% 1.21/0.99  ------ Superposition Simplification Setup
% 1.21/0.99  
% 1.21/0.99  --sup_indices_passive                   []
% 1.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_full_bw                           [BwDemod]
% 1.21/0.99  --sup_immed_triv                        [TrivRules]
% 1.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_immed_bw_main                     []
% 1.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.99  
% 1.21/0.99  ------ Combination Options
% 1.21/0.99  
% 1.21/0.99  --comb_res_mult                         3
% 1.21/0.99  --comb_sup_mult                         2
% 1.21/0.99  --comb_inst_mult                        10
% 1.21/0.99  
% 1.21/0.99  ------ Debug Options
% 1.21/0.99  
% 1.21/0.99  --dbg_backtrace                         false
% 1.21/0.99  --dbg_dump_prop_clauses                 false
% 1.21/0.99  --dbg_dump_prop_clauses_file            -
% 1.21/0.99  --dbg_out_stat                          false
% 1.21/0.99  ------ Parsing...
% 1.21/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.21/0.99  ------ Proving...
% 1.21/0.99  ------ Problem Properties 
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  clauses                                 12
% 1.21/0.99  conjectures                             3
% 1.21/0.99  EPR                                     1
% 1.21/0.99  Horn                                    10
% 1.21/0.99  unary                                   3
% 1.21/0.99  binary                                  5
% 1.21/0.99  lits                                    47
% 1.21/0.99  lits eq                                 9
% 1.21/0.99  fd_pure                                 0
% 1.21/0.99  fd_pseudo                               0
% 1.21/0.99  fd_cond                                 0
% 1.21/0.99  fd_pseudo_cond                          0
% 1.21/0.99  AC symbols                              0
% 1.21/0.99  
% 1.21/0.99  ------ Schedule dynamic 5 is on 
% 1.21/0.99  
% 1.21/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  ------ 
% 1.21/0.99  Current options:
% 1.21/0.99  ------ 
% 1.21/0.99  
% 1.21/0.99  ------ Input Options
% 1.21/0.99  
% 1.21/0.99  --out_options                           all
% 1.21/0.99  --tptp_safe_out                         true
% 1.21/0.99  --problem_path                          ""
% 1.21/0.99  --include_path                          ""
% 1.21/0.99  --clausifier                            res/vclausify_rel
% 1.21/0.99  --clausifier_options                    --mode clausify
% 1.21/0.99  --stdin                                 false
% 1.21/0.99  --stats_out                             all
% 1.21/0.99  
% 1.21/0.99  ------ General Options
% 1.21/0.99  
% 1.21/0.99  --fof                                   false
% 1.21/0.99  --time_out_real                         305.
% 1.21/0.99  --time_out_virtual                      -1.
% 1.21/0.99  --symbol_type_check                     false
% 1.21/0.99  --clausify_out                          false
% 1.21/0.99  --sig_cnt_out                           false
% 1.21/0.99  --trig_cnt_out                          false
% 1.21/0.99  --trig_cnt_out_tolerance                1.
% 1.21/0.99  --trig_cnt_out_sk_spl                   false
% 1.21/0.99  --abstr_cl_out                          false
% 1.21/0.99  
% 1.21/0.99  ------ Global Options
% 1.21/0.99  
% 1.21/0.99  --schedule                              default
% 1.21/0.99  --add_important_lit                     false
% 1.21/0.99  --prop_solver_per_cl                    1000
% 1.21/0.99  --min_unsat_core                        false
% 1.21/0.99  --soft_assumptions                      false
% 1.21/0.99  --soft_lemma_size                       3
% 1.21/0.99  --prop_impl_unit_size                   0
% 1.21/0.99  --prop_impl_unit                        []
% 1.21/0.99  --share_sel_clauses                     true
% 1.21/0.99  --reset_solvers                         false
% 1.21/0.99  --bc_imp_inh                            [conj_cone]
% 1.21/0.99  --conj_cone_tolerance                   3.
% 1.21/0.99  --extra_neg_conj                        none
% 1.21/0.99  --large_theory_mode                     true
% 1.21/0.99  --prolific_symb_bound                   200
% 1.21/0.99  --lt_threshold                          2000
% 1.21/0.99  --clause_weak_htbl                      true
% 1.21/0.99  --gc_record_bc_elim                     false
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing Options
% 1.21/0.99  
% 1.21/0.99  --preprocessing_flag                    true
% 1.21/0.99  --time_out_prep_mult                    0.1
% 1.21/0.99  --splitting_mode                        input
% 1.21/0.99  --splitting_grd                         true
% 1.21/0.99  --splitting_cvd                         false
% 1.21/0.99  --splitting_cvd_svl                     false
% 1.21/0.99  --splitting_nvd                         32
% 1.21/0.99  --sub_typing                            true
% 1.21/0.99  --prep_gs_sim                           true
% 1.21/0.99  --prep_unflatten                        true
% 1.21/0.99  --prep_res_sim                          true
% 1.21/0.99  --prep_upred                            true
% 1.21/0.99  --prep_sem_filter                       exhaustive
% 1.21/0.99  --prep_sem_filter_out                   false
% 1.21/0.99  --pred_elim                             true
% 1.21/0.99  --res_sim_input                         true
% 1.21/0.99  --eq_ax_congr_red                       true
% 1.21/0.99  --pure_diseq_elim                       true
% 1.21/0.99  --brand_transform                       false
% 1.21/0.99  --non_eq_to_eq                          false
% 1.21/0.99  --prep_def_merge                        true
% 1.21/0.99  --prep_def_merge_prop_impl              false
% 1.21/0.99  --prep_def_merge_mbd                    true
% 1.21/0.99  --prep_def_merge_tr_red                 false
% 1.21/0.99  --prep_def_merge_tr_cl                  false
% 1.21/0.99  --smt_preprocessing                     true
% 1.21/0.99  --smt_ac_axioms                         fast
% 1.21/0.99  --preprocessed_out                      false
% 1.21/0.99  --preprocessed_stats                    false
% 1.21/0.99  
% 1.21/0.99  ------ Abstraction refinement Options
% 1.21/0.99  
% 1.21/0.99  --abstr_ref                             []
% 1.21/0.99  --abstr_ref_prep                        false
% 1.21/0.99  --abstr_ref_until_sat                   false
% 1.21/0.99  --abstr_ref_sig_restrict                funpre
% 1.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/0.99  --abstr_ref_under                       []
% 1.21/0.99  
% 1.21/0.99  ------ SAT Options
% 1.21/0.99  
% 1.21/0.99  --sat_mode                              false
% 1.21/0.99  --sat_fm_restart_options                ""
% 1.21/0.99  --sat_gr_def                            false
% 1.21/0.99  --sat_epr_types                         true
% 1.21/0.99  --sat_non_cyclic_types                  false
% 1.21/0.99  --sat_finite_models                     false
% 1.21/0.99  --sat_fm_lemmas                         false
% 1.21/0.99  --sat_fm_prep                           false
% 1.21/0.99  --sat_fm_uc_incr                        true
% 1.21/0.99  --sat_out_model                         small
% 1.21/0.99  --sat_out_clauses                       false
% 1.21/0.99  
% 1.21/0.99  ------ QBF Options
% 1.21/0.99  
% 1.21/0.99  --qbf_mode                              false
% 1.21/0.99  --qbf_elim_univ                         false
% 1.21/0.99  --qbf_dom_inst                          none
% 1.21/0.99  --qbf_dom_pre_inst                      false
% 1.21/0.99  --qbf_sk_in                             false
% 1.21/0.99  --qbf_pred_elim                         true
% 1.21/0.99  --qbf_split                             512
% 1.21/0.99  
% 1.21/0.99  ------ BMC1 Options
% 1.21/0.99  
% 1.21/0.99  --bmc1_incremental                      false
% 1.21/0.99  --bmc1_axioms                           reachable_all
% 1.21/0.99  --bmc1_min_bound                        0
% 1.21/0.99  --bmc1_max_bound                        -1
% 1.21/0.99  --bmc1_max_bound_default                -1
% 1.21/0.99  --bmc1_symbol_reachability              true
% 1.21/0.99  --bmc1_property_lemmas                  false
% 1.21/0.99  --bmc1_k_induction                      false
% 1.21/0.99  --bmc1_non_equiv_states                 false
% 1.21/0.99  --bmc1_deadlock                         false
% 1.21/0.99  --bmc1_ucm                              false
% 1.21/0.99  --bmc1_add_unsat_core                   none
% 1.21/0.99  --bmc1_unsat_core_children              false
% 1.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/0.99  --bmc1_out_stat                         full
% 1.21/0.99  --bmc1_ground_init                      false
% 1.21/0.99  --bmc1_pre_inst_next_state              false
% 1.21/0.99  --bmc1_pre_inst_state                   false
% 1.21/0.99  --bmc1_pre_inst_reach_state             false
% 1.21/0.99  --bmc1_out_unsat_core                   false
% 1.21/0.99  --bmc1_aig_witness_out                  false
% 1.21/0.99  --bmc1_verbose                          false
% 1.21/0.99  --bmc1_dump_clauses_tptp                false
% 1.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.21/0.99  --bmc1_dump_file                        -
% 1.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.21/0.99  --bmc1_ucm_extend_mode                  1
% 1.21/0.99  --bmc1_ucm_init_mode                    2
% 1.21/0.99  --bmc1_ucm_cone_mode                    none
% 1.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.21/0.99  --bmc1_ucm_relax_model                  4
% 1.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/0.99  --bmc1_ucm_layered_model                none
% 1.21/0.99  --bmc1_ucm_max_lemma_size               10
% 1.21/0.99  
% 1.21/0.99  ------ AIG Options
% 1.21/0.99  
% 1.21/0.99  --aig_mode                              false
% 1.21/0.99  
% 1.21/0.99  ------ Instantiation Options
% 1.21/0.99  
% 1.21/0.99  --instantiation_flag                    true
% 1.21/0.99  --inst_sos_flag                         false
% 1.21/0.99  --inst_sos_phase                        true
% 1.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/0.99  --inst_lit_sel_side                     none
% 1.21/0.99  --inst_solver_per_active                1400
% 1.21/0.99  --inst_solver_calls_frac                1.
% 1.21/0.99  --inst_passive_queue_type               priority_queues
% 1.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/0.99  --inst_passive_queues_freq              [25;2]
% 1.21/0.99  --inst_dismatching                      true
% 1.21/0.99  --inst_eager_unprocessed_to_passive     true
% 1.21/0.99  --inst_prop_sim_given                   true
% 1.21/0.99  --inst_prop_sim_new                     false
% 1.21/0.99  --inst_subs_new                         false
% 1.21/0.99  --inst_eq_res_simp                      false
% 1.21/0.99  --inst_subs_given                       false
% 1.21/0.99  --inst_orphan_elimination               true
% 1.21/0.99  --inst_learning_loop_flag               true
% 1.21/0.99  --inst_learning_start                   3000
% 1.21/0.99  --inst_learning_factor                  2
% 1.21/0.99  --inst_start_prop_sim_after_learn       3
% 1.21/0.99  --inst_sel_renew                        solver
% 1.21/0.99  --inst_lit_activity_flag                true
% 1.21/0.99  --inst_restr_to_given                   false
% 1.21/0.99  --inst_activity_threshold               500
% 1.21/0.99  --inst_out_proof                        true
% 1.21/0.99  
% 1.21/0.99  ------ Resolution Options
% 1.21/0.99  
% 1.21/0.99  --resolution_flag                       false
% 1.21/0.99  --res_lit_sel                           adaptive
% 1.21/0.99  --res_lit_sel_side                      none
% 1.21/0.99  --res_ordering                          kbo
% 1.21/0.99  --res_to_prop_solver                    active
% 1.21/0.99  --res_prop_simpl_new                    false
% 1.21/0.99  --res_prop_simpl_given                  true
% 1.21/0.99  --res_passive_queue_type                priority_queues
% 1.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/0.99  --res_passive_queues_freq               [15;5]
% 1.21/0.99  --res_forward_subs                      full
% 1.21/0.99  --res_backward_subs                     full
% 1.21/0.99  --res_forward_subs_resolution           true
% 1.21/0.99  --res_backward_subs_resolution          true
% 1.21/0.99  --res_orphan_elimination                true
% 1.21/0.99  --res_time_limit                        2.
% 1.21/0.99  --res_out_proof                         true
% 1.21/0.99  
% 1.21/0.99  ------ Superposition Options
% 1.21/0.99  
% 1.21/0.99  --superposition_flag                    true
% 1.21/0.99  --sup_passive_queue_type                priority_queues
% 1.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.21/0.99  --demod_completeness_check              fast
% 1.21/0.99  --demod_use_ground                      true
% 1.21/0.99  --sup_to_prop_solver                    passive
% 1.21/0.99  --sup_prop_simpl_new                    true
% 1.21/0.99  --sup_prop_simpl_given                  true
% 1.21/0.99  --sup_fun_splitting                     false
% 1.21/0.99  --sup_smt_interval                      50000
% 1.21/0.99  
% 1.21/0.99  ------ Superposition Simplification Setup
% 1.21/0.99  
% 1.21/0.99  --sup_indices_passive                   []
% 1.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_full_bw                           [BwDemod]
% 1.21/0.99  --sup_immed_triv                        [TrivRules]
% 1.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_immed_bw_main                     []
% 1.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.99  
% 1.21/0.99  ------ Combination Options
% 1.21/0.99  
% 1.21/0.99  --comb_res_mult                         3
% 1.21/0.99  --comb_sup_mult                         2
% 1.21/0.99  --comb_inst_mult                        10
% 1.21/0.99  
% 1.21/0.99  ------ Debug Options
% 1.21/0.99  
% 1.21/0.99  --dbg_backtrace                         false
% 1.21/0.99  --dbg_dump_prop_clauses                 false
% 1.21/0.99  --dbg_dump_prop_clauses_file            -
% 1.21/0.99  --dbg_out_stat                          false
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  ------ Proving...
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  % SZS status Theorem for theBenchmark.p
% 1.21/0.99  
% 1.21/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.21/0.99  
% 1.21/0.99  fof(f10,conjecture,(
% 1.21/0.99    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f11,negated_conjecture,(
% 1.21/0.99    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.21/0.99    inference(negated_conjecture,[],[f10])).
% 1.21/0.99  
% 1.21/0.99  fof(f12,plain,(
% 1.21/0.99    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.21/0.99    inference(pure_predicate_removal,[],[f11])).
% 1.21/0.99  
% 1.21/0.99  fof(f29,plain,(
% 1.21/0.99    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f12])).
% 1.21/0.99  
% 1.21/0.99  fof(f30,plain,(
% 1.21/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.21/0.99    inference(flattening,[],[f29])).
% 1.21/0.99  
% 1.21/0.99  fof(f36,plain,(
% 1.21/0.99    ( ! [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k6_waybel_0(X0,sK2),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.21/0.99    introduced(choice_axiom,[])).
% 1.21/0.99  
% 1.21/0.99  fof(f35,plain,(
% 1.21/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK1,X1),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.21/0.99    introduced(choice_axiom,[])).
% 1.21/0.99  
% 1.21/0.99  fof(f37,plain,(
% 1.21/0.99    (~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f36,f35])).
% 1.21/0.99  
% 1.21/0.99  fof(f60,plain,(
% 1.21/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f9,axiom,(
% 1.21/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f27,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f9])).
% 1.21/0.99  
% 1.21/0.99  fof(f28,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.21/0.99    inference(flattening,[],[f27])).
% 1.21/0.99  
% 1.21/0.99  fof(f52,plain,(
% 1.21/0.99    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f28])).
% 1.21/0.99  
% 1.21/0.99  fof(f58,plain,(
% 1.21/0.99    v2_lattice3(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f55,plain,(
% 1.21/0.99    v3_orders_2(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f56,plain,(
% 1.21/0.99    v5_orders_2(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f59,plain,(
% 1.21/0.99    l1_waybel_9(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f7,axiom,(
% 1.21/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f24,plain,(
% 1.21/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.21/0.99    inference(ennf_transformation,[],[f7])).
% 1.21/0.99  
% 1.21/0.99  fof(f50,plain,(
% 1.21/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f24])).
% 1.21/0.99  
% 1.21/0.99  fof(f1,axiom,(
% 1.21/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f13,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(ennf_transformation,[],[f1])).
% 1.21/0.99  
% 1.21/0.99  fof(f14,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(flattening,[],[f13])).
% 1.21/0.99  
% 1.21/0.99  fof(f31,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(nnf_transformation,[],[f14])).
% 1.21/0.99  
% 1.21/0.99  fof(f32,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(rectify,[],[f31])).
% 1.21/0.99  
% 1.21/0.99  fof(f33,plain,(
% 1.21/0.99    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.21/0.99    introduced(choice_axiom,[])).
% 1.21/0.99  
% 1.21/0.99  fof(f34,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.21/0.99  
% 1.21/0.99  fof(f38,plain,(
% 1.21/0.99    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f34])).
% 1.21/0.99  
% 1.21/0.99  fof(f6,axiom,(
% 1.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f22,plain,(
% 1.21/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f6])).
% 1.21/0.99  
% 1.21/0.99  fof(f23,plain,(
% 1.21/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.21/0.99    inference(flattening,[],[f22])).
% 1.21/0.99  
% 1.21/0.99  fof(f47,plain,(
% 1.21/0.99    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f23])).
% 1.21/0.99  
% 1.21/0.99  fof(f57,plain,(
% 1.21/0.99    v1_lattice3(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f5,axiom,(
% 1.21/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f20,plain,(
% 1.21/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.21/0.99    inference(ennf_transformation,[],[f5])).
% 1.21/0.99  
% 1.21/0.99  fof(f21,plain,(
% 1.21/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.21/0.99    inference(flattening,[],[f20])).
% 1.21/0.99  
% 1.21/0.99  fof(f45,plain,(
% 1.21/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f21])).
% 1.21/0.99  
% 1.21/0.99  fof(f46,plain,(
% 1.21/0.99    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f23])).
% 1.21/0.99  
% 1.21/0.99  fof(f49,plain,(
% 1.21/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f24])).
% 1.21/0.99  
% 1.21/0.99  fof(f61,plain,(
% 1.21/0.99    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f48,plain,(
% 1.21/0.99    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f23])).
% 1.21/0.99  
% 1.21/0.99  fof(f4,axiom,(
% 1.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f18,plain,(
% 1.21/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f4])).
% 1.21/0.99  
% 1.21/0.99  fof(f19,plain,(
% 1.21/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.21/0.99    inference(flattening,[],[f18])).
% 1.21/0.99  
% 1.21/0.99  fof(f44,plain,(
% 1.21/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f19])).
% 1.21/0.99  
% 1.21/0.99  fof(f2,axiom,(
% 1.21/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f15,plain,(
% 1.21/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.21/0.99    inference(ennf_transformation,[],[f2])).
% 1.21/0.99  
% 1.21/0.99  fof(f42,plain,(
% 1.21/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f15])).
% 1.21/0.99  
% 1.21/0.99  fof(f3,axiom,(
% 1.21/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f16,plain,(
% 1.21/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f3])).
% 1.21/0.99  
% 1.21/0.99  fof(f17,plain,(
% 1.21/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.99    inference(flattening,[],[f16])).
% 1.21/0.99  
% 1.21/0.99  fof(f43,plain,(
% 1.21/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f17])).
% 1.21/0.99  
% 1.21/0.99  fof(f8,axiom,(
% 1.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.99  
% 1.21/0.99  fof(f25,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.21/0.99    inference(ennf_transformation,[],[f8])).
% 1.21/0.99  
% 1.21/0.99  fof(f26,plain,(
% 1.21/0.99    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.99    inference(flattening,[],[f25])).
% 1.21/0.99  
% 1.21/0.99  fof(f51,plain,(
% 1.21/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.21/0.99    inference(cnf_transformation,[],[f26])).
% 1.21/0.99  
% 1.21/0.99  fof(f54,plain,(
% 1.21/0.99    v8_pre_topc(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f53,plain,(
% 1.21/0.99    v2_pre_topc(sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  fof(f62,plain,(
% 1.21/0.99    ~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)),
% 1.21/0.99    inference(cnf_transformation,[],[f37])).
% 1.21/0.99  
% 1.21/0.99  cnf(c_17,negated_conjecture,
% 1.21/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1110,negated_conjecture,
% 1.21/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1376,plain,
% 1.21/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_14,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | ~ v3_orders_2(X1)
% 1.21/0.99      | ~ v5_orders_2(X1)
% 1.21/0.99      | ~ v2_lattice3(X1)
% 1.21/0.99      | ~ l1_orders_2(X1)
% 1.21/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_19,negated_conjecture,
% 1.21/0.99      ( v2_lattice3(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_376,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | ~ v3_orders_2(X1)
% 1.21/0.99      | ~ v5_orders_2(X1)
% 1.21/0.99      | ~ l1_orders_2(X1)
% 1.21/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
% 1.21/0.99      | sK1 != X1 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_377,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | ~ v3_orders_2(sK1)
% 1.21/0.99      | ~ v5_orders_2(sK1)
% 1.21/0.99      | ~ l1_orders_2(sK1)
% 1.21/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_22,negated_conjecture,
% 1.21/0.99      ( v3_orders_2(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_21,negated_conjecture,
% 1.21/0.99      ( v5_orders_2(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_18,negated_conjecture,
% 1.21/0.99      ( l1_waybel_9(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_11,plain,
% 1.21/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_47,plain,
% 1.21/0.99      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_381,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_377,c_22,c_21,c_18,c_47]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1107,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 1.21/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),k6_domain_1(u1_struct_0(sK1),X0_55)) = k6_waybel_0(sK1,X0_55) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_381]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1379,plain,
% 1.21/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),k6_domain_1(u1_struct_0(sK1),X0_55)) = k6_waybel_0(sK1,X0_55)
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1597,plain,
% 1.21/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
% 1.21/0.99      inference(superposition,[status(thm)],[c_1376,c_1379]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_3,plain,
% 1.21/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.21/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 1.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/0.99      | ~ v4_pre_topc(X3,X2)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.21/0.99      | ~ l1_pre_topc(X2)
% 1.21/0.99      | ~ l1_pre_topc(X1)
% 1.21/0.99      | ~ v1_funct_1(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_9,plain,
% 1.21/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.21/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.21/0.99      | ~ l1_orders_2(X0)
% 1.21/0.99      | v2_struct_0(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_304,plain,
% 1.21/0.99      ( l1_orders_2(X0) | sK1 != X0 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_305,plain,
% 1.21/0.99      ( l1_orders_2(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_304]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_433,plain,
% 1.21/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.21/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.21/0.99      | v2_struct_0(X0)
% 1.21/0.99      | sK1 != X0 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_305]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_434,plain,
% 1.21/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | v2_struct_0(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_20,negated_conjecture,
% 1.21/0.99      ( v1_lattice3(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_7,plain,
% 1.21/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_59,plain,
% 1.21/0.99      ( ~ l1_orders_2(sK1) | ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_438,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_434,c_20,c_18,c_47,c_59]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_439,plain,
% 1.21/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_438]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_488,plain,
% 1.21/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 1.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 1.21/0.99      | ~ v4_pre_topc(X3,X2)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.21/0.99      | ~ l1_pre_topc(X2)
% 1.21/0.99      | ~ l1_pre_topc(X1)
% 1.21/0.99      | ~ v1_funct_1(X0)
% 1.21/0.99      | k4_waybel_1(sK1,X4) != X0
% 1.21/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_439]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_489,plain,
% 1.21/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.21/0.99      | ~ v4_pre_topc(X3,X2)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.21/0.99      | ~ l1_pre_topc(X2)
% 1.21/0.99      | ~ l1_pre_topc(X1)
% 1.21/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 1.21/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_10,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | ~ l1_orders_2(X1)
% 1.21/0.99      | v2_struct_0(X1)
% 1.21/0.99      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 1.21/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_397,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | v2_struct_0(X1)
% 1.21/0.99      | v1_funct_1(k4_waybel_1(X1,X0))
% 1.21/0.99      | sK1 != X1 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_305]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_398,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | v2_struct_0(sK1)
% 1.21/0.99      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_493,plain,
% 1.21/0.99      ( ~ l1_pre_topc(X1)
% 1.21/0.99      | ~ l1_pre_topc(X2)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.21/0.99      | ~ v4_pre_topc(X3,X2)
% 1.21/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/0.99      | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.21/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_489,c_20,c_18,c_47,c_59,c_398]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_494,plain,
% 1.21/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.21/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.21/0.99      | ~ v4_pre_topc(X3,X2)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.21/0.99      | ~ l1_pre_topc(X2)
% 1.21/0.99      | ~ l1_pre_topc(X1)
% 1.21/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_493]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1104,plain,
% 1.21/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_55),X0_56,X1_56)
% 1.21/0.99      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_56)))
% 1.21/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 1.21/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 1.21/0.99      | ~ v4_pre_topc(X1_55,X1_56)
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),k4_waybel_1(sK1,X0_55),X1_55),X0_56)
% 1.21/0.99      | ~ l1_pre_topc(X1_56)
% 1.21/0.99      | ~ l1_pre_topc(X0_56)
% 1.21/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_494]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1382,plain,
% 1.21/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK1)
% 1.21/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 1.21/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_55),X1_56,X0_56) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) != iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,X0_56) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1_56),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),X1_56) = iProver_top
% 1.21/0.99      | l1_pre_topc(X0_56) != iProver_top
% 1.21/0.99      | l1_pre_topc(X1_56) != iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1104]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1828,plain,
% 1.21/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK1)
% 1.21/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,X0_56) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
% 1.21/0.99      | l1_pre_topc(X0_56) != iProver_top
% 1.21/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.21/0.99      inference(equality_resolution,[status(thm)],[c_1382]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_31,plain,
% 1.21/0.99      ( l1_waybel_9(sK1) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_12,plain,
% 1.21/0.99      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_43,plain,
% 1.21/0.99      ( l1_waybel_9(X0) != iProver_top | l1_pre_topc(X0) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_45,plain,
% 1.21/0.99      ( l1_waybel_9(sK1) != iProver_top
% 1.21/0.99      | l1_pre_topc(sK1) = iProver_top ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1888,plain,
% 1.21/0.99      ( l1_pre_topc(X0_56) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,X0_56) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 1.21/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
% 1.21/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK1) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_1828,c_31,c_45]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1889,plain,
% 1.21/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK1)
% 1.21/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,X0_56) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_56)))) != iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,X0_56) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_56),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
% 1.21/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_1888]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1900,plain,
% 1.21/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,sK1) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
% 1.21/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.21/0.99      inference(equality_resolution,[status(thm)],[c_1889]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_16,negated_conjecture,
% 1.21/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1111,negated_conjecture,
% 1.21/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1)
% 1.21/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1140,plain,
% 1.21/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_55),sK1,sK1) = iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_8,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.21/0.99      | ~ l1_orders_2(X1)
% 1.21/0.99      | v2_struct_0(X1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_415,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.21/0.99      | v2_struct_0(X1)
% 1.21/0.99      | sK1 != X1 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_305]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_416,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.21/0.99      | v2_struct_0(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_420,plain,
% 1.21/0.99      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_416,c_20,c_18,c_47,c_59]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_421,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_420]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1106,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_421]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1151,plain,
% 1.21/0.99      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1987,plain,
% 1.21/0.99      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_55),X1_55),sK1) = iProver_top
% 1.21/0.99      | v4_pre_topc(X1_55,sK1) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.21/0.99      | m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_1900,c_31,c_45,c_1140,c_1151]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1988,plain,
% 1.21/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.21/0.99      | m1_subset_1(X1_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | v4_pre_topc(X0_55,sK1) != iProver_top
% 1.21/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_55),X0_55),sK1) = iProver_top ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_1987]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1997,plain,
% 1.21/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.21/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
% 1.21/0.99      inference(superposition,[status(thm)],[c_1597,c_1988]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_6,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,X1)
% 1.21/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.21/0.99      | v1_xboole_0(X1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_4,plain,
% 1.21/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_5,plain,
% 1.21/0.99      ( v2_struct_0(X0)
% 1.21/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.21/0.99      | ~ l1_struct_0(X0) ),
% 1.21/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_315,plain,
% 1.21/0.99      ( v2_struct_0(X0)
% 1.21/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.21/0.99      | ~ l1_pre_topc(X0) ),
% 1.21/0.99      inference(resolution,[status(thm)],[c_4,c_5]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_284,plain,
% 1.21/0.99      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK1 != X0 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_285,plain,
% 1.21/0.99      ( ~ l1_orders_2(sK1) | ~ v2_struct_0(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_287,plain,
% 1.21/0.99      ( ~ v2_struct_0(sK1) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_285,c_20,c_18,c_47,c_59]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_460,plain,
% 1.21/0.99      ( ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_315,c_287]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_461,plain,
% 1.21/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) | ~ l1_pre_topc(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_44,plain,
% 1.21/0.99      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_65,plain,
% 1.21/0.99      ( v2_struct_0(sK1)
% 1.21/0.99      | ~ v1_xboole_0(u1_struct_0(sK1))
% 1.21/0.99      | ~ l1_struct_0(sK1) ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_68,plain,
% 1.21/0.99      ( l1_struct_0(sK1) | ~ l1_pre_topc(sK1) ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_463,plain,
% 1.21/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_461,c_20,c_18,c_44,c_47,c_59,c_65,c_68]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_473,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,X1)
% 1.21/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.21/0.99      | u1_struct_0(sK1) != X1 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_463]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_474,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1105,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 1.21/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_55),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_474]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1154,plain,
% 1.21/0.99      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1105]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1156,plain,
% 1.21/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.21/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_13,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X0),X1)
% 1.21/0.99      | ~ v2_pre_topc(X1)
% 1.21/0.99      | ~ v8_pre_topc(X1)
% 1.21/0.99      | v2_struct_0(X1)
% 1.21/0.99      | ~ l1_pre_topc(X1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_23,negated_conjecture,
% 1.21/0.99      ( v8_pre_topc(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_355,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(X1),X0),X1)
% 1.21/0.99      | ~ v2_pre_topc(X1)
% 1.21/0.99      | v2_struct_0(X1)
% 1.21/0.99      | ~ l1_pre_topc(X1)
% 1.21/0.99      | sK1 != X1 ),
% 1.21/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_356,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.21/0.99      | ~ v2_pre_topc(sK1)
% 1.21/0.99      | v2_struct_0(sK1)
% 1.21/0.99      | ~ l1_pre_topc(sK1) ),
% 1.21/0.99      inference(unflattening,[status(thm)],[c_355]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_24,negated_conjecture,
% 1.21/0.99      ( v2_pre_topc(sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_360,plain,
% 1.21/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.21/0.99      inference(global_propositional_subsumption,
% 1.21/0.99                [status(thm)],
% 1.21/0.99                [c_356,c_24,c_20,c_18,c_44,c_47,c_59]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_361,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
% 1.21/0.99      inference(renaming,[status(thm)],[c_360]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1108,plain,
% 1.21/0.99      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_55),sK1) ),
% 1.21/0.99      inference(subtyping,[status(esa)],[c_361]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1145,plain,
% 1.21/0.99      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_55),sK1) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_1147,plain,
% 1.21/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.21/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
% 1.21/0.99      inference(instantiation,[status(thm)],[c_1145]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_15,negated_conjecture,
% 1.21/0.99      ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
% 1.21/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_36,plain,
% 1.21/0.99      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(c_32,plain,
% 1.21/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.21/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.21/0.99  
% 1.21/0.99  cnf(contradiction,plain,
% 1.21/0.99      ( $false ),
% 1.21/0.99      inference(minisat,[status(thm)],[c_1997,c_1156,c_1147,c_36,c_32]) ).
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.21/0.99  
% 1.21/0.99  ------                               Statistics
% 1.21/0.99  
% 1.21/0.99  ------ General
% 1.21/0.99  
% 1.21/0.99  abstr_ref_over_cycles:                  0
% 1.21/0.99  abstr_ref_under_cycles:                 0
% 1.21/0.99  gc_basic_clause_elim:                   0
% 1.21/0.99  forced_gc_time:                         0
% 1.21/0.99  parsing_time:                           0.01
% 1.21/0.99  unif_index_cands_time:                  0.
% 1.21/0.99  unif_index_add_time:                    0.
% 1.21/0.99  orderings_time:                         0.
% 1.21/0.99  out_proof_time:                         0.011
% 1.21/0.99  total_time:                             0.105
% 1.21/0.99  num_of_symbols:                         61
% 1.21/0.99  num_of_terms:                           1886
% 1.21/0.99  
% 1.21/0.99  ------ Preprocessing
% 1.21/0.99  
% 1.21/0.99  num_of_splits:                          0
% 1.21/0.99  num_of_split_atoms:                     0
% 1.21/0.99  num_of_reused_defs:                     0
% 1.21/0.99  num_eq_ax_congr_red:                    24
% 1.21/0.99  num_of_sem_filtered_clauses:            1
% 1.21/0.99  num_of_subtypes:                        3
% 1.21/0.99  monotx_restored_types:                  0
% 1.21/0.99  sat_num_of_epr_types:                   0
% 1.21/0.99  sat_num_of_non_cyclic_types:            0
% 1.21/0.99  sat_guarded_non_collapsed_types:        0
% 1.21/0.99  num_pure_diseq_elim:                    0
% 1.21/0.99  simp_replaced_by:                       0
% 1.21/0.99  res_preprocessed:                       88
% 1.21/0.99  prep_upred:                             0
% 1.21/0.99  prep_unflattend:                        19
% 1.21/0.99  smt_new_axioms:                         0
% 1.21/0.99  pred_elim_cands:                        4
% 1.21/0.99  pred_elim:                              13
% 1.21/0.99  pred_elim_cl:                           13
% 1.21/0.99  pred_elim_cycles:                       16
% 1.21/0.99  merged_defs:                            0
% 1.21/0.99  merged_defs_ncl:                        0
% 1.21/0.99  bin_hyper_res:                          0
% 1.21/0.99  prep_cycles:                            4
% 1.21/0.99  pred_elim_time:                         0.018
% 1.21/0.99  splitting_time:                         0.
% 1.21/0.99  sem_filter_time:                        0.
% 1.21/0.99  monotx_time:                            0.
% 1.21/0.99  subtype_inf_time:                       0.
% 1.21/0.99  
% 1.21/0.99  ------ Problem properties
% 1.21/0.99  
% 1.21/0.99  clauses:                                12
% 1.21/0.99  conjectures:                            3
% 1.21/0.99  epr:                                    1
% 1.21/0.99  horn:                                   10
% 1.21/0.99  ground:                                 3
% 1.21/0.99  unary:                                  3
% 1.21/0.99  binary:                                 5
% 1.21/0.99  lits:                                   47
% 1.21/0.99  lits_eq:                                9
% 1.21/0.99  fd_pure:                                0
% 1.21/0.99  fd_pseudo:                              0
% 1.21/0.99  fd_cond:                                0
% 1.21/0.99  fd_pseudo_cond:                         0
% 1.21/0.99  ac_symbols:                             0
% 1.21/0.99  
% 1.21/0.99  ------ Propositional Solver
% 1.21/0.99  
% 1.21/0.99  prop_solver_calls:                      26
% 1.21/0.99  prop_fast_solver_calls:                 906
% 1.21/0.99  smt_solver_calls:                       0
% 1.21/0.99  smt_fast_solver_calls:                  0
% 1.21/0.99  prop_num_of_clauses:                    457
% 1.21/0.99  prop_preprocess_simplified:             2633
% 1.21/0.99  prop_fo_subsumed:                       25
% 1.21/0.99  prop_solver_time:                       0.
% 1.21/0.99  smt_solver_time:                        0.
% 1.21/0.99  smt_fast_solver_time:                   0.
% 1.21/0.99  prop_fast_solver_time:                  0.
% 1.21/0.99  prop_unsat_core_time:                   0.
% 1.21/0.99  
% 1.21/0.99  ------ QBF
% 1.21/0.99  
% 1.21/0.99  qbf_q_res:                              0
% 1.21/0.99  qbf_num_tautologies:                    0
% 1.21/0.99  qbf_prep_cycles:                        0
% 1.21/0.99  
% 1.21/0.99  ------ BMC1
% 1.21/0.99  
% 1.21/0.99  bmc1_current_bound:                     -1
% 1.21/0.99  bmc1_last_solved_bound:                 -1
% 1.21/0.99  bmc1_unsat_core_size:                   -1
% 1.21/0.99  bmc1_unsat_core_parents_size:           -1
% 1.21/0.99  bmc1_merge_next_fun:                    0
% 1.21/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.21/0.99  
% 1.21/0.99  ------ Instantiation
% 1.21/0.99  
% 1.21/0.99  inst_num_of_clauses:                    111
% 1.21/0.99  inst_num_in_passive:                    21
% 1.21/0.99  inst_num_in_active:                     85
% 1.21/0.99  inst_num_in_unprocessed:                5
% 1.21/0.99  inst_num_of_loops:                      90
% 1.21/0.99  inst_num_of_learning_restarts:          0
% 1.21/0.99  inst_num_moves_active_passive:          1
% 1.21/0.99  inst_lit_activity:                      0
% 1.21/0.99  inst_lit_activity_moves:                0
% 1.21/0.99  inst_num_tautologies:                   0
% 1.21/0.99  inst_num_prop_implied:                  0
% 1.21/0.99  inst_num_existing_simplified:           0
% 1.21/0.99  inst_num_eq_res_simplified:             0
% 1.21/0.99  inst_num_child_elim:                    0
% 1.21/0.99  inst_num_of_dismatching_blockings:      24
% 1.21/0.99  inst_num_of_non_proper_insts:           96
% 1.21/0.99  inst_num_of_duplicates:                 0
% 1.21/0.99  inst_inst_num_from_inst_to_res:         0
% 1.21/0.99  inst_dismatching_checking_time:         0.
% 1.21/0.99  
% 1.21/0.99  ------ Resolution
% 1.21/0.99  
% 1.21/0.99  res_num_of_clauses:                     0
% 1.21/0.99  res_num_in_passive:                     0
% 1.21/0.99  res_num_in_active:                      0
% 1.21/0.99  res_num_of_loops:                       92
% 1.21/0.99  res_forward_subset_subsumed:            16
% 1.21/0.99  res_backward_subset_subsumed:           0
% 1.21/0.99  res_forward_subsumed:                   0
% 1.21/0.99  res_backward_subsumed:                  0
% 1.21/0.99  res_forward_subsumption_resolution:     1
% 1.21/0.99  res_backward_subsumption_resolution:    0
% 1.21/0.99  res_clause_to_clause_subsumption:       22
% 1.21/0.99  res_orphan_elimination:                 0
% 1.21/0.99  res_tautology_del:                      32
% 1.21/0.99  res_num_eq_res_simplified:              0
% 1.21/0.99  res_num_sel_changes:                    0
% 1.21/0.99  res_moves_from_active_to_pass:          0
% 1.21/0.99  
% 1.21/0.99  ------ Superposition
% 1.21/0.99  
% 1.21/0.99  sup_time_total:                         0.
% 1.21/0.99  sup_time_generating:                    0.
% 1.21/0.99  sup_time_sim_full:                      0.
% 1.21/0.99  sup_time_sim_immed:                     0.
% 1.21/0.99  
% 1.21/0.99  sup_num_of_clauses:                     19
% 1.21/0.99  sup_num_in_active:                      18
% 1.21/0.99  sup_num_in_passive:                     1
% 1.21/0.99  sup_num_of_loops:                       17
% 1.21/0.99  sup_fw_superposition:                   2
% 1.21/0.99  sup_bw_superposition:                   0
% 1.21/0.99  sup_immediate_simplified:               3
% 1.21/0.99  sup_given_eliminated:                   0
% 1.21/0.99  comparisons_done:                       0
% 1.21/0.99  comparisons_avoided:                    0
% 1.21/0.99  
% 1.21/0.99  ------ Simplifications
% 1.21/0.99  
% 1.21/0.99  
% 1.21/0.99  sim_fw_subset_subsumed:                 3
% 1.21/0.99  sim_bw_subset_subsumed:                 0
% 1.21/0.99  sim_fw_subsumed:                        0
% 1.21/0.99  sim_bw_subsumed:                        0
% 1.21/0.99  sim_fw_subsumption_res:                 0
% 1.21/0.99  sim_bw_subsumption_res:                 0
% 1.21/0.99  sim_tautology_del:                      0
% 1.21/0.99  sim_eq_tautology_del:                   0
% 1.21/0.99  sim_eq_res_simp:                        0
% 1.21/0.99  sim_fw_demodulated:                     0
% 1.21/0.99  sim_bw_demodulated:                     0
% 1.21/0.99  sim_light_normalised:                   0
% 1.21/0.99  sim_joinable_taut:                      0
% 1.21/0.99  sim_joinable_simp:                      0
% 1.21/0.99  sim_ac_normalised:                      0
% 1.21/0.99  sim_smt_subsumption:                    0
% 1.21/0.99  
%------------------------------------------------------------------------------
