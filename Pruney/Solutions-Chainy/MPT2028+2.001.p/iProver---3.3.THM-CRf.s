%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:54 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 650 expanded)
%              Number of clauses        :   98 ( 187 expanded)
%              Number of leaves         :   14 ( 147 expanded)
%              Depth                    :   28
%              Number of atoms          :  682 (4599 expanded)
%              Number of equality atoms :  124 ( 136 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f32])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f39,f38])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v8_pre_topc(X0)
           => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1114,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1427,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_48,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_23,c_22,c_19,c_48])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),k6_domain_1(u1_struct_0(sK1),X0_54)) = k6_waybel_0(sK1,X0_54) ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_1431,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),k6_domain_1(u1_struct_0(sK1),X0_54)) = k6_waybel_0(sK1,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_1735,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1427,c_1431])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_291,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_292,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_63,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_294,plain,
    ( ~ v2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_21,c_19,c_48,c_63])).

cnf(c_443,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_294])).

cnf(c_444,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_19,c_48])).

cnf(c_449,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_473,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k4_waybel_1(sK1,X4) != X0
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_449])).

cnf(c_474,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_294])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_478,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
    | ~ v4_pre_topc(X3,X2)
    | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_19,c_48,c_390])).

cnf(c_479,plain,
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
    inference(renaming,[status(thm)],[c_478])).

cnf(c_1107,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_54),X0_55,X1_55)
    | ~ v4_pre_topc(X1_54,X1_55)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k4_waybel_1(sK1,X0_54),X1_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_1434,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_54),X1_55,X0_55) != iProver_top
    | v4_pre_topc(X1_54,X0_55) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),X1_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_2063,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
    | v4_pre_topc(X1_54,X0_55) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1434])).

cnf(c_32,plain,
    ( l1_waybel_9(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_44,plain,
    ( l1_waybel_9(X0) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_46,plain,
    ( l1_waybel_9(sK1) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_2247,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
    | v4_pre_topc(X1_54,X0_55) != iProver_top
    | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_32,c_46])).

cnf(c_2248,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
    | v4_pre_topc(X1_54,X0_55) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2247])).

cnf(c_2259,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1) != iProver_top
    | v4_pre_topc(X1_54,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2248])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1115,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1147,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_294])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_19,c_48])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_1161,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_2423,plain,
    ( v4_pre_topc(X1_54,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_32,c_46,c_1147,c_1161])).

cnf(c_2424,plain,
    ( v4_pre_topc(X0_54,sK1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_54),X0_54),sK1) = iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2423])).

cnf(c_2433,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_2424])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_294])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_430,plain,
    ( m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_19,c_48])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_1433,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_waybel_0(sK1,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1118,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1423,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_xboole_0(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_1832,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK1,X0_54)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_1423])).

cnf(c_1849,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK1,sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_1,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_343,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_344,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_45,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_19,c_45])).

cnf(c_349,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_1111,plain,
    ( v4_pre_topc(X0_54,sK1)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_1430,plain,
    ( v4_pre_topc(X0_54,sK1) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_1831,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,X0_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK1,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_1430])).

cnf(c_1846,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(k6_waybel_0(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(k6_domain_1(X1_54,X0_54),k1_zfmisc_1(X1_54))
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1587,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1588,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1587])).

cnf(c_14,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_322,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_323,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_25,c_21,c_19,c_45,c_48,c_63])).

cnf(c_328,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_1112,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_54),sK1)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_1152,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_54),sK1) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_1154,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,plain,
    ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2433,c_1849,c_1846,c_1588,c_1154,c_37,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.50/0.98  
% 1.50/0.98  ------  iProver source info
% 1.50/0.98  
% 1.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.50/0.98  git: non_committed_changes: false
% 1.50/0.98  git: last_make_outside_of_git: false
% 1.50/0.98  
% 1.50/0.98  ------ 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options
% 1.50/0.98  
% 1.50/0.98  --out_options                           all
% 1.50/0.98  --tptp_safe_out                         true
% 1.50/0.98  --problem_path                          ""
% 1.50/0.98  --include_path                          ""
% 1.50/0.98  --clausifier                            res/vclausify_rel
% 1.50/0.98  --clausifier_options                    --mode clausify
% 1.50/0.98  --stdin                                 false
% 1.50/0.98  --stats_out                             all
% 1.50/0.98  
% 1.50/0.98  ------ General Options
% 1.50/0.98  
% 1.50/0.98  --fof                                   false
% 1.50/0.98  --time_out_real                         305.
% 1.50/0.98  --time_out_virtual                      -1.
% 1.50/0.98  --symbol_type_check                     false
% 1.50/0.98  --clausify_out                          false
% 1.50/0.98  --sig_cnt_out                           false
% 1.50/0.98  --trig_cnt_out                          false
% 1.50/0.98  --trig_cnt_out_tolerance                1.
% 1.50/0.98  --trig_cnt_out_sk_spl                   false
% 1.50/0.98  --abstr_cl_out                          false
% 1.50/0.98  
% 1.50/0.98  ------ Global Options
% 1.50/0.98  
% 1.50/0.98  --schedule                              default
% 1.50/0.98  --add_important_lit                     false
% 1.50/0.98  --prop_solver_per_cl                    1000
% 1.50/0.98  --min_unsat_core                        false
% 1.50/0.98  --soft_assumptions                      false
% 1.50/0.98  --soft_lemma_size                       3
% 1.50/0.98  --prop_impl_unit_size                   0
% 1.50/0.98  --prop_impl_unit                        []
% 1.50/0.98  --share_sel_clauses                     true
% 1.50/0.98  --reset_solvers                         false
% 1.50/0.98  --bc_imp_inh                            [conj_cone]
% 1.50/0.98  --conj_cone_tolerance                   3.
% 1.50/0.98  --extra_neg_conj                        none
% 1.50/0.98  --large_theory_mode                     true
% 1.50/0.98  --prolific_symb_bound                   200
% 1.50/0.98  --lt_threshold                          2000
% 1.50/0.98  --clause_weak_htbl                      true
% 1.50/0.98  --gc_record_bc_elim                     false
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing Options
% 1.50/0.98  
% 1.50/0.98  --preprocessing_flag                    true
% 1.50/0.98  --time_out_prep_mult                    0.1
% 1.50/0.98  --splitting_mode                        input
% 1.50/0.98  --splitting_grd                         true
% 1.50/0.98  --splitting_cvd                         false
% 1.50/0.98  --splitting_cvd_svl                     false
% 1.50/0.98  --splitting_nvd                         32
% 1.50/0.98  --sub_typing                            true
% 1.50/0.98  --prep_gs_sim                           true
% 1.50/0.98  --prep_unflatten                        true
% 1.50/0.98  --prep_res_sim                          true
% 1.50/0.98  --prep_upred                            true
% 1.50/0.98  --prep_sem_filter                       exhaustive
% 1.50/0.98  --prep_sem_filter_out                   false
% 1.50/0.98  --pred_elim                             true
% 1.50/0.98  --res_sim_input                         true
% 1.50/0.98  --eq_ax_congr_red                       true
% 1.50/0.98  --pure_diseq_elim                       true
% 1.50/0.98  --brand_transform                       false
% 1.50/0.98  --non_eq_to_eq                          false
% 1.50/0.98  --prep_def_merge                        true
% 1.50/0.98  --prep_def_merge_prop_impl              false
% 1.50/0.98  --prep_def_merge_mbd                    true
% 1.50/0.98  --prep_def_merge_tr_red                 false
% 1.50/0.98  --prep_def_merge_tr_cl                  false
% 1.50/0.98  --smt_preprocessing                     true
% 1.50/0.98  --smt_ac_axioms                         fast
% 1.50/0.98  --preprocessed_out                      false
% 1.50/0.98  --preprocessed_stats                    false
% 1.50/0.98  
% 1.50/0.98  ------ Abstraction refinement Options
% 1.50/0.98  
% 1.50/0.98  --abstr_ref                             []
% 1.50/0.98  --abstr_ref_prep                        false
% 1.50/0.98  --abstr_ref_until_sat                   false
% 1.50/0.98  --abstr_ref_sig_restrict                funpre
% 1.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.98  --abstr_ref_under                       []
% 1.50/0.98  
% 1.50/0.98  ------ SAT Options
% 1.50/0.98  
% 1.50/0.98  --sat_mode                              false
% 1.50/0.98  --sat_fm_restart_options                ""
% 1.50/0.98  --sat_gr_def                            false
% 1.50/0.98  --sat_epr_types                         true
% 1.50/0.98  --sat_non_cyclic_types                  false
% 1.50/0.98  --sat_finite_models                     false
% 1.50/0.98  --sat_fm_lemmas                         false
% 1.50/0.98  --sat_fm_prep                           false
% 1.50/0.98  --sat_fm_uc_incr                        true
% 1.50/0.98  --sat_out_model                         small
% 1.50/0.98  --sat_out_clauses                       false
% 1.50/0.98  
% 1.50/0.98  ------ QBF Options
% 1.50/0.98  
% 1.50/0.98  --qbf_mode                              false
% 1.50/0.98  --qbf_elim_univ                         false
% 1.50/0.98  --qbf_dom_inst                          none
% 1.50/0.98  --qbf_dom_pre_inst                      false
% 1.50/0.98  --qbf_sk_in                             false
% 1.50/0.98  --qbf_pred_elim                         true
% 1.50/0.98  --qbf_split                             512
% 1.50/0.98  
% 1.50/0.98  ------ BMC1 Options
% 1.50/0.98  
% 1.50/0.98  --bmc1_incremental                      false
% 1.50/0.98  --bmc1_axioms                           reachable_all
% 1.50/0.98  --bmc1_min_bound                        0
% 1.50/0.98  --bmc1_max_bound                        -1
% 1.50/0.98  --bmc1_max_bound_default                -1
% 1.50/0.98  --bmc1_symbol_reachability              true
% 1.50/0.98  --bmc1_property_lemmas                  false
% 1.50/0.98  --bmc1_k_induction                      false
% 1.50/0.98  --bmc1_non_equiv_states                 false
% 1.50/0.98  --bmc1_deadlock                         false
% 1.50/0.98  --bmc1_ucm                              false
% 1.50/0.98  --bmc1_add_unsat_core                   none
% 1.50/0.98  --bmc1_unsat_core_children              false
% 1.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.98  --bmc1_out_stat                         full
% 1.50/0.98  --bmc1_ground_init                      false
% 1.50/0.98  --bmc1_pre_inst_next_state              false
% 1.50/0.98  --bmc1_pre_inst_state                   false
% 1.50/0.98  --bmc1_pre_inst_reach_state             false
% 1.50/0.98  --bmc1_out_unsat_core                   false
% 1.50/0.98  --bmc1_aig_witness_out                  false
% 1.50/0.98  --bmc1_verbose                          false
% 1.50/0.98  --bmc1_dump_clauses_tptp                false
% 1.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.98  --bmc1_dump_file                        -
% 1.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.98  --bmc1_ucm_extend_mode                  1
% 1.50/0.98  --bmc1_ucm_init_mode                    2
% 1.50/0.98  --bmc1_ucm_cone_mode                    none
% 1.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.98  --bmc1_ucm_relax_model                  4
% 1.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.98  --bmc1_ucm_layered_model                none
% 1.50/0.98  --bmc1_ucm_max_lemma_size               10
% 1.50/0.98  
% 1.50/0.98  ------ AIG Options
% 1.50/0.98  
% 1.50/0.98  --aig_mode                              false
% 1.50/0.98  
% 1.50/0.98  ------ Instantiation Options
% 1.50/0.98  
% 1.50/0.98  --instantiation_flag                    true
% 1.50/0.98  --inst_sos_flag                         false
% 1.50/0.98  --inst_sos_phase                        true
% 1.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel_side                     num_symb
% 1.50/0.98  --inst_solver_per_active                1400
% 1.50/0.98  --inst_solver_calls_frac                1.
% 1.50/0.98  --inst_passive_queue_type               priority_queues
% 1.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.98  --inst_passive_queues_freq              [25;2]
% 1.50/0.98  --inst_dismatching                      true
% 1.50/0.98  --inst_eager_unprocessed_to_passive     true
% 1.50/0.98  --inst_prop_sim_given                   true
% 1.50/0.98  --inst_prop_sim_new                     false
% 1.50/0.98  --inst_subs_new                         false
% 1.50/0.98  --inst_eq_res_simp                      false
% 1.50/0.98  --inst_subs_given                       false
% 1.50/0.98  --inst_orphan_elimination               true
% 1.50/0.98  --inst_learning_loop_flag               true
% 1.50/0.98  --inst_learning_start                   3000
% 1.50/0.98  --inst_learning_factor                  2
% 1.50/0.98  --inst_start_prop_sim_after_learn       3
% 1.50/0.98  --inst_sel_renew                        solver
% 1.50/0.98  --inst_lit_activity_flag                true
% 1.50/0.98  --inst_restr_to_given                   false
% 1.50/0.98  --inst_activity_threshold               500
% 1.50/0.98  --inst_out_proof                        true
% 1.50/0.98  
% 1.50/0.98  ------ Resolution Options
% 1.50/0.98  
% 1.50/0.98  --resolution_flag                       true
% 1.50/0.98  --res_lit_sel                           adaptive
% 1.50/0.98  --res_lit_sel_side                      none
% 1.50/0.98  --res_ordering                          kbo
% 1.50/0.98  --res_to_prop_solver                    active
% 1.50/0.98  --res_prop_simpl_new                    false
% 1.50/0.98  --res_prop_simpl_given                  true
% 1.50/0.98  --res_passive_queue_type                priority_queues
% 1.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.98  --res_passive_queues_freq               [15;5]
% 1.50/0.98  --res_forward_subs                      full
% 1.50/0.98  --res_backward_subs                     full
% 1.50/0.98  --res_forward_subs_resolution           true
% 1.50/0.98  --res_backward_subs_resolution          true
% 1.50/0.98  --res_orphan_elimination                true
% 1.50/0.98  --res_time_limit                        2.
% 1.50/0.98  --res_out_proof                         true
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Options
% 1.50/0.98  
% 1.50/0.98  --superposition_flag                    true
% 1.50/0.98  --sup_passive_queue_type                priority_queues
% 1.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.98  --demod_completeness_check              fast
% 1.50/0.98  --demod_use_ground                      true
% 1.50/0.98  --sup_to_prop_solver                    passive
% 1.50/0.98  --sup_prop_simpl_new                    true
% 1.50/0.98  --sup_prop_simpl_given                  true
% 1.50/0.98  --sup_fun_splitting                     false
% 1.50/0.98  --sup_smt_interval                      50000
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Simplification Setup
% 1.50/0.98  
% 1.50/0.98  --sup_indices_passive                   []
% 1.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_full_bw                           [BwDemod]
% 1.50/0.98  --sup_immed_triv                        [TrivRules]
% 1.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_immed_bw_main                     []
% 1.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  
% 1.50/0.98  ------ Combination Options
% 1.50/0.98  
% 1.50/0.98  --comb_res_mult                         3
% 1.50/0.98  --comb_sup_mult                         2
% 1.50/0.98  --comb_inst_mult                        10
% 1.50/0.98  
% 1.50/0.98  ------ Debug Options
% 1.50/0.98  
% 1.50/0.98  --dbg_backtrace                         false
% 1.50/0.98  --dbg_dump_prop_clauses                 false
% 1.50/0.98  --dbg_dump_prop_clauses_file            -
% 1.50/0.98  --dbg_out_stat                          false
% 1.50/0.98  ------ Parsing...
% 1.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.50/0.98  ------ Proving...
% 1.50/0.98  ------ Problem Properties 
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  clauses                                 15
% 1.50/0.98  conjectures                             3
% 1.50/0.98  EPR                                     1
% 1.50/0.98  Horn                                    12
% 1.50/0.98  unary                                   3
% 1.50/0.98  binary                                  5
% 1.50/0.98  lits                                    56
% 1.50/0.98  lits eq                                 9
% 1.50/0.98  fd_pure                                 0
% 1.50/0.98  fd_pseudo                               0
% 1.50/0.98  fd_cond                                 0
% 1.50/0.98  fd_pseudo_cond                          0
% 1.50/0.98  AC symbols                              0
% 1.50/0.98  
% 1.50/0.98  ------ Schedule dynamic 5 is on 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  ------ 
% 1.50/0.98  Current options:
% 1.50/0.98  ------ 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options
% 1.50/0.98  
% 1.50/0.98  --out_options                           all
% 1.50/0.98  --tptp_safe_out                         true
% 1.50/0.98  --problem_path                          ""
% 1.50/0.98  --include_path                          ""
% 1.50/0.98  --clausifier                            res/vclausify_rel
% 1.50/0.98  --clausifier_options                    --mode clausify
% 1.50/0.98  --stdin                                 false
% 1.50/0.98  --stats_out                             all
% 1.50/0.98  
% 1.50/0.98  ------ General Options
% 1.50/0.98  
% 1.50/0.98  --fof                                   false
% 1.50/0.98  --time_out_real                         305.
% 1.50/0.98  --time_out_virtual                      -1.
% 1.50/0.98  --symbol_type_check                     false
% 1.50/0.98  --clausify_out                          false
% 1.50/0.98  --sig_cnt_out                           false
% 1.50/0.98  --trig_cnt_out                          false
% 1.50/0.98  --trig_cnt_out_tolerance                1.
% 1.50/0.98  --trig_cnt_out_sk_spl                   false
% 1.50/0.98  --abstr_cl_out                          false
% 1.50/0.98  
% 1.50/0.98  ------ Global Options
% 1.50/0.98  
% 1.50/0.98  --schedule                              default
% 1.50/0.98  --add_important_lit                     false
% 1.50/0.98  --prop_solver_per_cl                    1000
% 1.50/0.98  --min_unsat_core                        false
% 1.50/0.98  --soft_assumptions                      false
% 1.50/0.98  --soft_lemma_size                       3
% 1.50/0.98  --prop_impl_unit_size                   0
% 1.50/0.98  --prop_impl_unit                        []
% 1.50/0.98  --share_sel_clauses                     true
% 1.50/0.98  --reset_solvers                         false
% 1.50/0.98  --bc_imp_inh                            [conj_cone]
% 1.50/0.98  --conj_cone_tolerance                   3.
% 1.50/0.98  --extra_neg_conj                        none
% 1.50/0.98  --large_theory_mode                     true
% 1.50/0.98  --prolific_symb_bound                   200
% 1.50/0.98  --lt_threshold                          2000
% 1.50/0.98  --clause_weak_htbl                      true
% 1.50/0.98  --gc_record_bc_elim                     false
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing Options
% 1.50/0.98  
% 1.50/0.98  --preprocessing_flag                    true
% 1.50/0.98  --time_out_prep_mult                    0.1
% 1.50/0.98  --splitting_mode                        input
% 1.50/0.98  --splitting_grd                         true
% 1.50/0.98  --splitting_cvd                         false
% 1.50/0.98  --splitting_cvd_svl                     false
% 1.50/0.98  --splitting_nvd                         32
% 1.50/0.98  --sub_typing                            true
% 1.50/0.98  --prep_gs_sim                           true
% 1.50/0.98  --prep_unflatten                        true
% 1.50/0.98  --prep_res_sim                          true
% 1.50/0.98  --prep_upred                            true
% 1.50/0.98  --prep_sem_filter                       exhaustive
% 1.50/0.98  --prep_sem_filter_out                   false
% 1.50/0.98  --pred_elim                             true
% 1.50/0.98  --res_sim_input                         true
% 1.50/0.98  --eq_ax_congr_red                       true
% 1.50/0.98  --pure_diseq_elim                       true
% 1.50/0.98  --brand_transform                       false
% 1.50/0.98  --non_eq_to_eq                          false
% 1.50/0.98  --prep_def_merge                        true
% 1.50/0.98  --prep_def_merge_prop_impl              false
% 1.50/0.98  --prep_def_merge_mbd                    true
% 1.50/0.98  --prep_def_merge_tr_red                 false
% 1.50/0.98  --prep_def_merge_tr_cl                  false
% 1.50/0.98  --smt_preprocessing                     true
% 1.50/0.98  --smt_ac_axioms                         fast
% 1.50/0.98  --preprocessed_out                      false
% 1.50/0.98  --preprocessed_stats                    false
% 1.50/0.98  
% 1.50/0.98  ------ Abstraction refinement Options
% 1.50/0.98  
% 1.50/0.98  --abstr_ref                             []
% 1.50/0.98  --abstr_ref_prep                        false
% 1.50/0.98  --abstr_ref_until_sat                   false
% 1.50/0.98  --abstr_ref_sig_restrict                funpre
% 1.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.98  --abstr_ref_under                       []
% 1.50/0.98  
% 1.50/0.98  ------ SAT Options
% 1.50/0.98  
% 1.50/0.98  --sat_mode                              false
% 1.50/0.98  --sat_fm_restart_options                ""
% 1.50/0.98  --sat_gr_def                            false
% 1.50/0.98  --sat_epr_types                         true
% 1.50/0.98  --sat_non_cyclic_types                  false
% 1.50/0.98  --sat_finite_models                     false
% 1.50/0.98  --sat_fm_lemmas                         false
% 1.50/0.98  --sat_fm_prep                           false
% 1.50/0.98  --sat_fm_uc_incr                        true
% 1.50/0.98  --sat_out_model                         small
% 1.50/0.98  --sat_out_clauses                       false
% 1.50/0.98  
% 1.50/0.98  ------ QBF Options
% 1.50/0.98  
% 1.50/0.98  --qbf_mode                              false
% 1.50/0.98  --qbf_elim_univ                         false
% 1.50/0.98  --qbf_dom_inst                          none
% 1.50/0.98  --qbf_dom_pre_inst                      false
% 1.50/0.98  --qbf_sk_in                             false
% 1.50/0.98  --qbf_pred_elim                         true
% 1.50/0.98  --qbf_split                             512
% 1.50/0.98  
% 1.50/0.98  ------ BMC1 Options
% 1.50/0.98  
% 1.50/0.98  --bmc1_incremental                      false
% 1.50/0.98  --bmc1_axioms                           reachable_all
% 1.50/0.98  --bmc1_min_bound                        0
% 1.50/0.98  --bmc1_max_bound                        -1
% 1.50/0.98  --bmc1_max_bound_default                -1
% 1.50/0.98  --bmc1_symbol_reachability              true
% 1.50/0.98  --bmc1_property_lemmas                  false
% 1.50/0.98  --bmc1_k_induction                      false
% 1.50/0.98  --bmc1_non_equiv_states                 false
% 1.50/0.98  --bmc1_deadlock                         false
% 1.50/0.98  --bmc1_ucm                              false
% 1.50/0.98  --bmc1_add_unsat_core                   none
% 1.50/0.98  --bmc1_unsat_core_children              false
% 1.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.98  --bmc1_out_stat                         full
% 1.50/0.98  --bmc1_ground_init                      false
% 1.50/0.98  --bmc1_pre_inst_next_state              false
% 1.50/0.98  --bmc1_pre_inst_state                   false
% 1.50/0.98  --bmc1_pre_inst_reach_state             false
% 1.50/0.98  --bmc1_out_unsat_core                   false
% 1.50/0.98  --bmc1_aig_witness_out                  false
% 1.50/0.98  --bmc1_verbose                          false
% 1.50/0.98  --bmc1_dump_clauses_tptp                false
% 1.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.98  --bmc1_dump_file                        -
% 1.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.98  --bmc1_ucm_extend_mode                  1
% 1.50/0.98  --bmc1_ucm_init_mode                    2
% 1.50/0.98  --bmc1_ucm_cone_mode                    none
% 1.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.98  --bmc1_ucm_relax_model                  4
% 1.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.98  --bmc1_ucm_layered_model                none
% 1.50/0.98  --bmc1_ucm_max_lemma_size               10
% 1.50/0.98  
% 1.50/0.98  ------ AIG Options
% 1.50/0.98  
% 1.50/0.98  --aig_mode                              false
% 1.50/0.98  
% 1.50/0.98  ------ Instantiation Options
% 1.50/0.98  
% 1.50/0.98  --instantiation_flag                    true
% 1.50/0.98  --inst_sos_flag                         false
% 1.50/0.98  --inst_sos_phase                        true
% 1.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel_side                     none
% 1.50/0.98  --inst_solver_per_active                1400
% 1.50/0.98  --inst_solver_calls_frac                1.
% 1.50/0.98  --inst_passive_queue_type               priority_queues
% 1.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.98  --inst_passive_queues_freq              [25;2]
% 1.50/0.98  --inst_dismatching                      true
% 1.50/0.98  --inst_eager_unprocessed_to_passive     true
% 1.50/0.98  --inst_prop_sim_given                   true
% 1.50/0.98  --inst_prop_sim_new                     false
% 1.50/0.98  --inst_subs_new                         false
% 1.50/0.98  --inst_eq_res_simp                      false
% 1.50/0.98  --inst_subs_given                       false
% 1.50/0.98  --inst_orphan_elimination               true
% 1.50/0.98  --inst_learning_loop_flag               true
% 1.50/0.98  --inst_learning_start                   3000
% 1.50/0.98  --inst_learning_factor                  2
% 1.50/0.98  --inst_start_prop_sim_after_learn       3
% 1.50/0.98  --inst_sel_renew                        solver
% 1.50/0.98  --inst_lit_activity_flag                true
% 1.50/0.98  --inst_restr_to_given                   false
% 1.50/0.98  --inst_activity_threshold               500
% 1.50/0.98  --inst_out_proof                        true
% 1.50/0.98  
% 1.50/0.98  ------ Resolution Options
% 1.50/0.98  
% 1.50/0.98  --resolution_flag                       false
% 1.50/0.98  --res_lit_sel                           adaptive
% 1.50/0.98  --res_lit_sel_side                      none
% 1.50/0.98  --res_ordering                          kbo
% 1.50/0.98  --res_to_prop_solver                    active
% 1.50/0.98  --res_prop_simpl_new                    false
% 1.50/0.98  --res_prop_simpl_given                  true
% 1.50/0.98  --res_passive_queue_type                priority_queues
% 1.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.98  --res_passive_queues_freq               [15;5]
% 1.50/0.98  --res_forward_subs                      full
% 1.50/0.98  --res_backward_subs                     full
% 1.50/0.98  --res_forward_subs_resolution           true
% 1.50/0.98  --res_backward_subs_resolution          true
% 1.50/0.98  --res_orphan_elimination                true
% 1.50/0.98  --res_time_limit                        2.
% 1.50/0.98  --res_out_proof                         true
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Options
% 1.50/0.98  
% 1.50/0.98  --superposition_flag                    true
% 1.50/0.98  --sup_passive_queue_type                priority_queues
% 1.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.98  --demod_completeness_check              fast
% 1.50/0.98  --demod_use_ground                      true
% 1.50/0.98  --sup_to_prop_solver                    passive
% 1.50/0.98  --sup_prop_simpl_new                    true
% 1.50/0.98  --sup_prop_simpl_given                  true
% 1.50/0.98  --sup_fun_splitting                     false
% 1.50/0.98  --sup_smt_interval                      50000
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Simplification Setup
% 1.50/0.98  
% 1.50/0.98  --sup_indices_passive                   []
% 1.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_full_bw                           [BwDemod]
% 1.50/0.98  --sup_immed_triv                        [TrivRules]
% 1.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_immed_bw_main                     []
% 1.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  
% 1.50/0.98  ------ Combination Options
% 1.50/0.98  
% 1.50/0.98  --comb_res_mult                         3
% 1.50/0.98  --comb_sup_mult                         2
% 1.50/0.98  --comb_inst_mult                        10
% 1.50/0.98  
% 1.50/0.98  ------ Debug Options
% 1.50/0.98  
% 1.50/0.98  --dbg_backtrace                         false
% 1.50/0.98  --dbg_dump_prop_clauses                 false
% 1.50/0.98  --dbg_dump_prop_clauses_file            -
% 1.50/0.98  --dbg_out_stat                          false
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  ------ Proving...
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  % SZS status Theorem for theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  fof(f11,conjecture,(
% 1.50/0.98    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f12,negated_conjecture,(
% 1.50/0.98    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.50/0.98    inference(negated_conjecture,[],[f11])).
% 1.50/0.98  
% 1.50/0.98  fof(f13,plain,(
% 1.50/0.98    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.50/0.98    inference(pure_predicate_removal,[],[f12])).
% 1.50/0.98  
% 1.50/0.98  fof(f32,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f13])).
% 1.50/0.98  
% 1.50/0.98  fof(f33,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.50/0.98    inference(flattening,[],[f32])).
% 1.50/0.98  
% 1.50/0.98  fof(f39,plain,(
% 1.50/0.98    ( ! [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k6_waybel_0(X0,sK2),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f38,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK1,X1),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f40,plain,(
% 1.50/0.98    (~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f39,f38])).
% 1.50/0.98  
% 1.50/0.98  fof(f64,plain,(
% 1.50/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.50/0.98    inference(cnf_transformation,[],[f40])).
% 1.50/0.98  
% 1.50/0.98  fof(f10,axiom,(
% 1.50/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f30,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f10])).
% 1.50/0.99  
% 1.50/0.99  fof(f31,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.50/0.99    inference(flattening,[],[f30])).
% 1.50/0.99  
% 1.50/0.99  fof(f56,plain,(
% 1.50/0.99    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f31])).
% 1.50/0.99  
% 1.50/0.99  fof(f62,plain,(
% 1.50/0.99    v2_lattice3(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f59,plain,(
% 1.50/0.99    v3_orders_2(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f60,plain,(
% 1.50/0.99    v5_orders_2(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f63,plain,(
% 1.50/0.99    l1_waybel_9(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f8,axiom,(
% 1.50/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f27,plain,(
% 1.50/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.50/0.99    inference(ennf_transformation,[],[f8])).
% 1.50/0.99  
% 1.50/0.99  fof(f54,plain,(
% 1.50/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f27])).
% 1.50/0.99  
% 1.50/0.99  fof(f3,axiom,(
% 1.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f17,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.99    inference(ennf_transformation,[],[f3])).
% 1.50/0.99  
% 1.50/0.99  fof(f18,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.99    inference(flattening,[],[f17])).
% 1.50/0.99  
% 1.50/0.99  fof(f34,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.99    inference(nnf_transformation,[],[f18])).
% 1.50/0.99  
% 1.50/0.99  fof(f35,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.99    inference(rectify,[],[f34])).
% 1.50/0.99  
% 1.50/0.99  fof(f36,plain,(
% 1.50/0.99    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.50/0.99    introduced(choice_axiom,[])).
% 1.50/0.99  
% 1.50/0.99  fof(f37,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 1.50/0.99  
% 1.50/0.99  fof(f43,plain,(
% 1.50/0.99    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f37])).
% 1.50/0.99  
% 1.50/0.99  fof(f7,axiom,(
% 1.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f25,plain,(
% 1.50/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.99    inference(ennf_transformation,[],[f7])).
% 1.50/0.99  
% 1.50/0.99  fof(f26,plain,(
% 1.50/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.99    inference(flattening,[],[f25])).
% 1.50/0.99  
% 1.50/0.99  fof(f51,plain,(
% 1.50/0.99    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f26])).
% 1.50/0.99  
% 1.50/0.99  fof(f5,axiom,(
% 1.50/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f21,plain,(
% 1.50/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.50/0.99    inference(ennf_transformation,[],[f5])).
% 1.50/0.99  
% 1.50/0.99  fof(f22,plain,(
% 1.50/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.50/0.99    inference(flattening,[],[f21])).
% 1.50/0.99  
% 1.50/0.99  fof(f48,plain,(
% 1.50/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f22])).
% 1.50/0.99  
% 1.50/0.99  fof(f61,plain,(
% 1.50/0.99    v1_lattice3(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f50,plain,(
% 1.50/0.99    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f26])).
% 1.50/0.99  
% 1.50/0.99  fof(f53,plain,(
% 1.50/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f27])).
% 1.50/0.99  
% 1.50/0.99  fof(f65,plain,(
% 1.50/0.99    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f52,plain,(
% 1.50/0.99    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f26])).
% 1.50/0.99  
% 1.50/0.99  fof(f6,axiom,(
% 1.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f23,plain,(
% 1.50/0.99    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.99    inference(ennf_transformation,[],[f6])).
% 1.50/0.99  
% 1.50/0.99  fof(f24,plain,(
% 1.50/0.99    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.99    inference(flattening,[],[f23])).
% 1.50/0.99  
% 1.50/0.99  fof(f49,plain,(
% 1.50/0.99    ( ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f24])).
% 1.50/0.99  
% 1.50/0.99  fof(f1,axiom,(
% 1.50/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f14,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.50/0.99    inference(ennf_transformation,[],[f1])).
% 1.50/0.99  
% 1.50/0.99  fof(f41,plain,(
% 1.50/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f14])).
% 1.50/0.99  
% 1.50/0.99  fof(f2,axiom,(
% 1.50/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f15,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.99    inference(ennf_transformation,[],[f2])).
% 1.50/0.99  
% 1.50/0.99  fof(f16,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.99    inference(flattening,[],[f15])).
% 1.50/0.99  
% 1.50/0.99  fof(f42,plain,(
% 1.50/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f16])).
% 1.50/0.99  
% 1.50/0.99  fof(f57,plain,(
% 1.50/0.99    v2_pre_topc(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f4,axiom,(
% 1.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f19,plain,(
% 1.50/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.50/0.99    inference(ennf_transformation,[],[f4])).
% 1.50/0.99  
% 1.50/0.99  fof(f20,plain,(
% 1.50/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.50/0.99    inference(flattening,[],[f19])).
% 1.50/0.99  
% 1.50/0.99  fof(f47,plain,(
% 1.50/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f20])).
% 1.50/0.99  
% 1.50/0.99  fof(f9,axiom,(
% 1.50/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.99  
% 1.50/0.99  fof(f28,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.99    inference(ennf_transformation,[],[f9])).
% 1.50/0.99  
% 1.50/0.99  fof(f29,plain,(
% 1.50/0.99    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.99    inference(flattening,[],[f28])).
% 1.50/0.99  
% 1.50/0.99  fof(f55,plain,(
% 1.50/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.99    inference(cnf_transformation,[],[f29])).
% 1.50/0.99  
% 1.50/0.99  fof(f58,plain,(
% 1.50/0.99    v8_pre_topc(sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  fof(f66,plain,(
% 1.50/0.99    ~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)),
% 1.50/0.99    inference(cnf_transformation,[],[f40])).
% 1.50/0.99  
% 1.50/0.99  cnf(c_18,negated_conjecture,
% 1.50/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1114,negated_conjecture,
% 1.50/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1427,plain,
% 1.50/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_15,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | ~ v3_orders_2(X1)
% 1.50/0.99      | ~ v5_orders_2(X1)
% 1.50/0.99      | ~ v2_lattice3(X1)
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_20,negated_conjecture,
% 1.50/0.99      ( v2_lattice3(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_368,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | ~ v3_orders_2(X1)
% 1.50/0.99      | ~ v5_orders_2(X1)
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
% 1.50/0.99      | sK1 != X1 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_369,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | ~ v3_orders_2(sK1)
% 1.50/0.99      | ~ v5_orders_2(sK1)
% 1.50/0.99      | ~ l1_orders_2(sK1)
% 1.50/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_23,negated_conjecture,
% 1.50/0.99      ( v3_orders_2(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_22,negated_conjecture,
% 1.50/0.99      ( v5_orders_2(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_19,negated_conjecture,
% 1.50/0.99      ( l1_waybel_9(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_12,plain,
% 1.50/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_48,plain,
% 1.50/0.99      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_373,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_369,c_23,c_22,c_19,c_48]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1110,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 1.50/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),k6_domain_1(u1_struct_0(sK1),X0_54)) = k6_waybel_0(sK1,X0_54) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_373]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1431,plain,
% 1.50/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),k6_domain_1(u1_struct_0(sK1),X0_54)) = k6_waybel_0(sK1,X0_54)
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1735,plain,
% 1.50/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
% 1.50/0.99      inference(superposition,[status(thm)],[c_1427,c_1431]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_5,plain,
% 1.50/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.50/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 1.50/0.99      | ~ v4_pre_topc(X3,X2)
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.50/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.50/0.99      | ~ v1_funct_1(X0)
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X2) ),
% 1.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_10,plain,
% 1.50/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.50/0.99      | ~ l1_orders_2(X0)
% 1.50/0.99      | v2_struct_0(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_7,plain,
% 1.50/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_21,negated_conjecture,
% 1.50/0.99      ( v1_lattice3(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_291,plain,
% 1.50/0.99      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK1 != X0 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_292,plain,
% 1.50/0.99      ( ~ l1_orders_2(sK1) | ~ v2_struct_0(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_63,plain,
% 1.50/0.99      ( ~ l1_orders_2(sK1) | ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_294,plain,
% 1.50/0.99      ( ~ v2_struct_0(sK1) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_292,c_21,c_19,c_48,c_63]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_443,plain,
% 1.50/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.50/0.99      | ~ l1_orders_2(X0)
% 1.50/0.99      | sK1 != X0 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_294]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_444,plain,
% 1.50/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | ~ l1_orders_2(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_448,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_444,c_19,c_48]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_449,plain,
% 1.50/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_448]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_473,plain,
% 1.50/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 1.50/0.99      | ~ v4_pre_topc(X3,X2)
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.50/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.50/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.50/0.99      | ~ v1_funct_1(X0)
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X2)
% 1.50/0.99      | k4_waybel_1(sK1,X4) != X0
% 1.50/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_449]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_474,plain,
% 1.50/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.50/0.99      | ~ v4_pre_topc(X3,X2)
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.50/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.50/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X2)
% 1.50/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_11,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | v2_struct_0(X1)
% 1.50/0.99      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 1.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_389,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | v1_funct_1(k4_waybel_1(X1,X0))
% 1.50/0.99      | sK1 != X1 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_294]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_390,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | ~ l1_orders_2(sK1)
% 1.50/0.99      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_478,plain,
% 1.50/0.99      ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.50/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.50/0.99      | ~ v4_pre_topc(X3,X2)
% 1.50/0.99      | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X2)
% 1.50/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_474,c_19,c_48,c_390]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_479,plain,
% 1.50/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.50/0.99      | ~ v4_pre_topc(X3,X2)
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.50/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X2)
% 1.50/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_478]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1107,plain,
% 1.50/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_54),X0_55,X1_55)
% 1.50/0.99      | ~ v4_pre_topc(X1_54,X1_55)
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_55),u1_struct_0(X1_55),k4_waybel_1(sK1,X0_54),X1_54),X0_55)
% 1.50/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 1.50/0.99      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X1_55)))
% 1.50/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.50/0.99      | ~ l1_pre_topc(X1_55)
% 1.50/0.99      | ~ l1_pre_topc(X0_55)
% 1.50/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_479]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1434,plain,
% 1.50/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 1.50/0.99      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 1.50/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_54),X1_55,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(X1_54,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1_55),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),X1_55) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 1.50/0.99      | l1_pre_topc(X1_55) != iProver_top
% 1.50/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2063,plain,
% 1.50/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 1.50/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(X1_54,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 1.50/0.99      | l1_pre_topc(X0_55) != iProver_top
% 1.50/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.50/0.99      inference(equality_resolution,[status(thm)],[c_1434]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_32,plain,
% 1.50/0.99      ( l1_waybel_9(sK1) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_13,plain,
% 1.50/0.99      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_44,plain,
% 1.50/0.99      ( l1_waybel_9(X0) != iProver_top | l1_pre_topc(X0) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_46,plain,
% 1.50/0.99      ( l1_waybel_9(sK1) != iProver_top
% 1.50/0.99      | l1_pre_topc(sK1) = iProver_top ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_44]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2247,plain,
% 1.50/0.99      ( l1_pre_topc(X0_55) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
% 1.50/0.99      | v4_pre_topc(X1_54,X0_55) != iProver_top
% 1.50/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
% 1.50/0.99      | u1_struct_0(X0_55) != u1_struct_0(sK1) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_2063,c_32,c_46]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2248,plain,
% 1.50/0.99      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 1.50/0.99      | v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(X1_54,X0_55) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0_55),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_55)))) != iProver_top
% 1.50/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_2247]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2259,plain,
% 1.50/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1) != iProver_top
% 1.50/0.99      | v4_pre_topc(X1_54,sK1) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 1.50/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.50/0.99      inference(equality_resolution,[status(thm)],[c_2248]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_17,negated_conjecture,
% 1.50/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1115,negated_conjecture,
% 1.50/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1)
% 1.50/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1147,plain,
% 1.50/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_54),sK1,sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_9,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | v2_struct_0(X1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_407,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | sK1 != X1 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_294]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_408,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.50/0.99      | ~ l1_orders_2(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_412,plain,
% 1.50/0.99      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_408,c_19,c_48]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_413,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_412]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1109,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_413]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1161,plain,
% 1.50/0.99      ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2423,plain,
% 1.50/0.99      ( v4_pre_topc(X1_54,sK1) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_54),X1_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_2259,c_32,c_46,c_1147,c_1161]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2424,plain,
% 1.50/0.99      ( v4_pre_topc(X0_54,sK1) != iProver_top
% 1.50/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_54),X0_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X1_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_2423]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_2433,plain,
% 1.50/0.99      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
% 1.50/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 1.50/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.50/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(superposition,[status(thm)],[c_1735,c_2424]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_8,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | v2_struct_0(X1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_425,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.50/0.99      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.50/0.99      | ~ l1_orders_2(X1)
% 1.50/0.99      | sK1 != X1 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_294]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_426,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ l1_orders_2(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_425]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_430,plain,
% 1.50/0.99      ( m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_426,c_19,c_48]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_431,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_430]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1108,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 1.50/0.99      | m1_subset_1(k6_waybel_0(sK1,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_431]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1433,plain,
% 1.50/0.99      ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | m1_subset_1(k6_waybel_0(sK1,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_0,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.50/0.99      | ~ v1_xboole_0(X1)
% 1.50/0.99      | v1_xboole_0(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1118,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 1.50/0.99      | ~ v1_xboole_0(X1_54)
% 1.50/0.99      | v1_xboole_0(X0_54) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1423,plain,
% 1.50/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 1.50/0.99      | v1_xboole_0(X1_54) != iProver_top
% 1.50/0.99      | v1_xboole_0(X0_54) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1832,plain,
% 1.50/0.99      ( m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v1_xboole_0(k6_waybel_0(sK1,X0_54)) = iProver_top
% 1.50/0.99      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(superposition,[status(thm)],[c_1433,c_1423]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1849,plain,
% 1.50/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v1_xboole_0(k6_waybel_0(sK1,sK2)) = iProver_top
% 1.50/0.99      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_1832]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1,plain,
% 1.50/0.99      ( v4_pre_topc(X0,X1)
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.50/0.99      | ~ v2_pre_topc(X1)
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ v1_xboole_0(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_25,negated_conjecture,
% 1.50/0.99      ( v2_pre_topc(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_343,plain,
% 1.50/0.99      ( v4_pre_topc(X0,X1)
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.50/0.99      | ~ l1_pre_topc(X1)
% 1.50/0.99      | ~ v1_xboole_0(X0)
% 1.50/0.99      | sK1 != X1 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_25]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_344,plain,
% 1.50/0.99      ( v4_pre_topc(X0,sK1)
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ l1_pre_topc(sK1)
% 1.50/0.99      | ~ v1_xboole_0(X0) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_45,plain,
% 1.50/0.99      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_348,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | v4_pre_topc(X0,sK1)
% 1.50/0.99      | ~ v1_xboole_0(X0) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_344,c_19,c_45]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_349,plain,
% 1.50/0.99      ( v4_pre_topc(X0,sK1)
% 1.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ v1_xboole_0(X0) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_348]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1111,plain,
% 1.50/0.99      ( v4_pre_topc(X0_54,sK1)
% 1.50/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ v1_xboole_0(X0_54) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_349]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1430,plain,
% 1.50/0.99      ( v4_pre_topc(X0_54,sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.50/0.99      | v1_xboole_0(X0_54) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1831,plain,
% 1.50/0.99      ( v4_pre_topc(k6_waybel_0(sK1,X0_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v1_xboole_0(k6_waybel_0(sK1,X0_54)) != iProver_top ),
% 1.50/0.99      inference(superposition,[status(thm)],[c_1433,c_1430]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1846,plain,
% 1.50/0.99      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v1_xboole_0(k6_waybel_0(sK1,sK2)) != iProver_top ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_1831]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_6,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,X1)
% 1.50/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.50/0.99      | v1_xboole_0(X1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1117,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0_54,X1_54)
% 1.50/0.99      | m1_subset_1(k6_domain_1(X1_54,X0_54),k1_zfmisc_1(X1_54))
% 1.50/0.99      | v1_xboole_0(X1_54) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1587,plain,
% 1.50/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.50/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_1117]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1588,plain,
% 1.50/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.50/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.50/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1587]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_14,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.50/0.99      | ~ v8_pre_topc(X0)
% 1.50/0.99      | v2_struct_0(X0)
% 1.50/0.99      | ~ v2_pre_topc(X0)
% 1.50/0.99      | ~ l1_pre_topc(X0) ),
% 1.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_24,negated_conjecture,
% 1.50/0.99      ( v8_pre_topc(sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_322,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.50/0.99      | v2_struct_0(X0)
% 1.50/0.99      | ~ v2_pre_topc(X0)
% 1.50/0.99      | ~ l1_pre_topc(X0)
% 1.50/0.99      | sK1 != X0 ),
% 1.50/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_323,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | v2_struct_0(sK1)
% 1.50/0.99      | ~ v2_pre_topc(sK1)
% 1.50/0.99      | ~ l1_pre_topc(sK1) ),
% 1.50/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_327,plain,
% 1.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.50/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
% 1.50/0.99      inference(global_propositional_subsumption,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_323,c_25,c_21,c_19,c_45,c_48,c_63]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_328,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(renaming,[status(thm)],[c_327]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1112,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_54),sK1)
% 1.50/0.99      | ~ m1_subset_1(X0_54,u1_struct_0(sK1)) ),
% 1.50/0.99      inference(subtyping,[status(esa)],[c_328]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1152,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_54),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1112]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_1154,plain,
% 1.50/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 1.50/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.50/0.99      inference(instantiation,[status(thm)],[c_1152]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_16,negated_conjecture,
% 1.50/0.99      ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
% 1.50/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_37,plain,
% 1.50/0.99      ( v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) != iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(c_33,plain,
% 1.50/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.50/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.50/0.99  
% 1.50/0.99  cnf(contradiction,plain,
% 1.50/0.99      ( $false ),
% 1.50/0.99      inference(minisat,
% 1.50/0.99                [status(thm)],
% 1.50/0.99                [c_2433,c_1849,c_1846,c_1588,c_1154,c_37,c_33]) ).
% 1.50/0.99  
% 1.50/0.99  
% 1.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.50/0.99  
% 1.50/0.99  ------                               Statistics
% 1.50/0.99  
% 1.50/0.99  ------ General
% 1.50/0.99  
% 1.50/0.99  abstr_ref_over_cycles:                  0
% 1.50/0.99  abstr_ref_under_cycles:                 0
% 1.50/0.99  gc_basic_clause_elim:                   0
% 1.50/0.99  forced_gc_time:                         0
% 1.50/0.99  parsing_time:                           0.01
% 1.50/0.99  unif_index_cands_time:                  0.
% 1.50/0.99  unif_index_add_time:                    0.
% 1.50/0.99  orderings_time:                         0.
% 1.50/0.99  out_proof_time:                         0.011
% 1.50/0.99  total_time:                             0.117
% 1.50/0.99  num_of_symbols:                         59
% 1.50/0.99  num_of_terms:                           2298
% 1.50/0.99  
% 1.50/0.99  ------ Preprocessing
% 1.50/0.99  
% 1.50/0.99  num_of_splits:                          0
% 1.50/0.99  num_of_split_atoms:                     0
% 1.50/0.99  num_of_reused_defs:                     0
% 1.50/0.99  num_eq_ax_congr_red:                    26
% 1.50/0.99  num_of_sem_filtered_clauses:            1
% 1.50/0.99  num_of_subtypes:                        2
% 1.50/0.99  monotx_restored_types:                  0
% 1.50/0.99  sat_num_of_epr_types:                   0
% 1.50/0.99  sat_num_of_non_cyclic_types:            0
% 1.50/0.99  sat_guarded_non_collapsed_types:        0
% 1.50/0.99  num_pure_diseq_elim:                    0
% 1.50/0.99  simp_replaced_by:                       0
% 1.50/0.99  res_preprocessed:                       94
% 1.50/0.99  prep_upred:                             0
% 1.50/0.99  prep_unflattend:                        18
% 1.50/0.99  smt_new_axioms:                         0
% 1.50/0.99  pred_elim_cands:                        5
% 1.50/0.99  pred_elim:                              11
% 1.50/0.99  pred_elim_cl:                           11
% 1.50/0.99  pred_elim_cycles:                       13
% 1.50/0.99  merged_defs:                            0
% 1.50/0.99  merged_defs_ncl:                        0
% 1.50/0.99  bin_hyper_res:                          0
% 1.50/0.99  prep_cycles:                            4
% 1.50/0.99  pred_elim_time:                         0.016
% 1.50/0.99  splitting_time:                         0.
% 1.50/0.99  sem_filter_time:                        0.
% 1.50/0.99  monotx_time:                            0.
% 1.50/0.99  subtype_inf_time:                       0.
% 1.50/0.99  
% 1.50/0.99  ------ Problem properties
% 1.50/0.99  
% 1.50/0.99  clauses:                                15
% 1.50/0.99  conjectures:                            3
% 1.50/0.99  epr:                                    1
% 1.50/0.99  horn:                                   12
% 1.50/0.99  ground:                                 3
% 1.50/0.99  unary:                                  3
% 1.50/0.99  binary:                                 5
% 1.50/0.99  lits:                                   56
% 1.50/0.99  lits_eq:                                9
% 1.50/0.99  fd_pure:                                0
% 1.50/0.99  fd_pseudo:                              0
% 1.50/0.99  fd_cond:                                0
% 1.50/0.99  fd_pseudo_cond:                         0
% 1.50/0.99  ac_symbols:                             0
% 1.50/0.99  
% 1.50/0.99  ------ Propositional Solver
% 1.50/0.99  
% 1.50/0.99  prop_solver_calls:                      26
% 1.50/0.99  prop_fast_solver_calls:                 980
% 1.50/0.99  smt_solver_calls:                       0
% 1.50/0.99  smt_fast_solver_calls:                  0
% 1.50/0.99  prop_num_of_clauses:                    619
% 1.50/0.99  prop_preprocess_simplified:             3191
% 1.50/0.99  prop_fo_subsumed:                       29
% 1.50/0.99  prop_solver_time:                       0.
% 1.50/0.99  smt_solver_time:                        0.
% 1.50/0.99  smt_fast_solver_time:                   0.
% 1.50/0.99  prop_fast_solver_time:                  0.
% 1.50/0.99  prop_unsat_core_time:                   0.
% 1.50/0.99  
% 1.50/0.99  ------ QBF
% 1.50/0.99  
% 1.50/0.99  qbf_q_res:                              0
% 1.50/0.99  qbf_num_tautologies:                    0
% 1.50/0.99  qbf_prep_cycles:                        0
% 1.50/0.99  
% 1.50/0.99  ------ BMC1
% 1.50/0.99  
% 1.50/0.99  bmc1_current_bound:                     -1
% 1.50/0.99  bmc1_last_solved_bound:                 -1
% 1.50/0.99  bmc1_unsat_core_size:                   -1
% 1.50/0.99  bmc1_unsat_core_parents_size:           -1
% 1.50/0.99  bmc1_merge_next_fun:                    0
% 1.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.50/0.99  
% 1.50/0.99  ------ Instantiation
% 1.50/0.99  
% 1.50/0.99  inst_num_of_clauses:                    171
% 1.50/0.99  inst_num_in_passive:                    39
% 1.50/0.99  inst_num_in_active:                     122
% 1.50/0.99  inst_num_in_unprocessed:                10
% 1.50/0.99  inst_num_of_loops:                      130
% 1.50/0.99  inst_num_of_learning_restarts:          0
% 1.50/0.99  inst_num_moves_active_passive:          3
% 1.50/0.99  inst_lit_activity:                      0
% 1.50/0.99  inst_lit_activity_moves:                0
% 1.50/0.99  inst_num_tautologies:                   0
% 1.50/0.99  inst_num_prop_implied:                  0
% 1.50/0.99  inst_num_existing_simplified:           0
% 1.50/0.99  inst_num_eq_res_simplified:             0
% 1.50/0.99  inst_num_child_elim:                    0
% 1.50/0.99  inst_num_of_dismatching_blockings:      34
% 1.50/0.99  inst_num_of_non_proper_insts:           171
% 1.50/0.99  inst_num_of_duplicates:                 0
% 1.50/0.99  inst_inst_num_from_inst_to_res:         0
% 1.50/0.99  inst_dismatching_checking_time:         0.
% 1.50/0.99  
% 1.50/0.99  ------ Resolution
% 1.50/0.99  
% 1.50/0.99  res_num_of_clauses:                     0
% 1.50/0.99  res_num_in_passive:                     0
% 1.50/0.99  res_num_in_active:                      0
% 1.50/0.99  res_num_of_loops:                       98
% 1.50/0.99  res_forward_subset_subsumed:            35
% 1.50/0.99  res_backward_subset_subsumed:           2
% 1.50/0.99  res_forward_subsumed:                   0
% 1.50/0.99  res_backward_subsumed:                  0
% 1.50/0.99  res_forward_subsumption_resolution:     1
% 1.50/0.99  res_backward_subsumption_resolution:    0
% 1.50/0.99  res_clause_to_clause_subsumption:       35
% 1.50/0.99  res_orphan_elimination:                 0
% 1.50/0.99  res_tautology_del:                      46
% 1.50/0.99  res_num_eq_res_simplified:              0
% 1.50/0.99  res_num_sel_changes:                    0
% 1.50/0.99  res_moves_from_active_to_pass:          0
% 1.50/0.99  
% 1.50/0.99  ------ Superposition
% 1.50/0.99  
% 1.50/0.99  sup_time_total:                         0.
% 1.50/0.99  sup_time_generating:                    0.
% 1.50/0.99  sup_time_sim_full:                      0.
% 1.50/0.99  sup_time_sim_immed:                     0.
% 1.50/0.99  
% 1.50/0.99  sup_num_of_clauses:                     26
% 1.50/0.99  sup_num_in_active:                      25
% 1.50/0.99  sup_num_in_passive:                     1
% 1.50/0.99  sup_num_of_loops:                       24
% 1.50/0.99  sup_fw_superposition:                   2
% 1.50/0.99  sup_bw_superposition:                   6
% 1.50/0.99  sup_immediate_simplified:               4
% 1.50/0.99  sup_given_eliminated:                   0
% 1.50/0.99  comparisons_done:                       0
% 1.50/0.99  comparisons_avoided:                    0
% 1.50/0.99  
% 1.50/0.99  ------ Simplifications
% 1.50/0.99  
% 1.50/0.99  
% 1.50/0.99  sim_fw_subset_subsumed:                 2
% 1.50/0.99  sim_bw_subset_subsumed:                 0
% 1.50/0.99  sim_fw_subsumed:                        2
% 1.50/0.99  sim_bw_subsumed:                        0
% 1.50/0.99  sim_fw_subsumption_res:                 0
% 1.50/0.99  sim_bw_subsumption_res:                 0
% 1.50/0.99  sim_tautology_del:                      1
% 1.50/0.99  sim_eq_tautology_del:                   0
% 1.50/0.99  sim_eq_res_simp:                        0
% 1.50/0.99  sim_fw_demodulated:                     0
% 1.50/0.99  sim_bw_demodulated:                     0
% 1.50/0.99  sim_light_normalised:                   0
% 1.50/0.99  sim_joinable_taut:                      0
% 1.50/0.99  sim_joinable_simp:                      0
% 1.50/0.99  sim_ac_normalised:                      0
% 1.50/0.99  sim_smt_subsumption:                    0
% 1.50/0.99  
%------------------------------------------------------------------------------
