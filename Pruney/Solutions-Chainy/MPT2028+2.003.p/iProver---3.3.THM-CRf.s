%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:54 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 581 expanded)
%              Number of clauses        :  104 ( 172 expanded)
%              Number of leaves         :   21 ( 136 expanded)
%              Depth                    :   23
%              Number of atoms          :  718 (4044 expanded)
%              Number of equality atoms :   76 (  81 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

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
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f45,f44])).

fof(f69,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1175,plain,
    ( ~ v4_pre_topc(X0_56,X0_57)
    | v4_pre_topc(X1_56,X0_57)
    | X1_56 != X0_56 ),
    theory(equality)).

cnf(c_2007,plain,
    ( v4_pre_topc(X0_56,X0_57)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X1_56),k6_domain_1(u1_struct_0(sK1),X2_56)),X0_57)
    | X0_56 != k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X1_56),k6_domain_1(u1_struct_0(sK1),X2_56)) ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_4176,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)),sK1)
    | v4_pre_topc(k6_waybel_0(sK1,X1_56),sK1)
    | k6_waybel_0(sK1,X1_56) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) ),
    inference(instantiation,[status(thm)],[c_2007])).

cnf(c_4178,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)),sK1)
    | v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)
    | k6_waybel_0(sK1,sK2) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_4176])).

cnf(c_1168,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_2213,plain,
    ( X0_56 != X1_56
    | k6_waybel_0(sK1,X2_56) != X1_56
    | k6_waybel_0(sK1,X2_56) = X0_56 ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2539,plain,
    ( X0_56 != k6_waybel_0(sK1,X1_56)
    | k6_waybel_0(sK1,X2_56) = X0_56
    | k6_waybel_0(sK1,X2_56) != k6_waybel_0(sK1,X1_56) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_3879,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) != k6_waybel_0(sK1,X0_56)
    | k6_waybel_0(sK1,X1_56) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56))
    | k6_waybel_0(sK1,X1_56) != k6_waybel_0(sK1,X0_56) ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_3880,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) != k6_waybel_0(sK1,sK2)
    | k6_waybel_0(sK1,sK2) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2))
    | k6_waybel_0(sK1,sK2) != k6_waybel_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3879])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | m1_subset_1(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_2041,plain,
    ( m1_subset_1(X0_56,X1_56)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X1_56 != k1_zfmisc_1(u1_struct_0(sK1))
    | X0_56 != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2253,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0_56)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_56 != k1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_2572,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_6,plain,
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

cnf(c_12,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_315,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_316,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_50,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_68,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_318,plain,
    ( ~ v2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_23,c_21,c_50,c_68])).

cnf(c_427,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_318])).

cnf(c_428,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_21,c_50])).

cnf(c_433,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_511,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_433])).

cnf(c_512,plain,
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
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_318])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_516,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_21,c_50,c_446])).

cnf(c_517,plain,
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
    inference(renaming,[status(thm)],[c_516])).

cnf(c_1153,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,X1_57)
    | ~ v4_pre_topc(X1_56,X1_57)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),k4_waybel_1(sK1,X0_56),X1_56),X0_57)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_57)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | u1_struct_0(X1_57) != u1_struct_0(sK1)
    | u1_struct_0(X0_57) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_517])).

cnf(c_1733,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,sK1)
    | ~ v4_pre_topc(X1_56,sK1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),X1_56),X0_57)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK1))))
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_57) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1959,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,sK1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X1_56)),X0_57)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X1_56),sK1)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK1))))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X1_56),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0_57) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_1961,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK2),sK1,sK1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)),sK1)
    | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1737,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0_56)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1835,plain,
    ( ~ m1_subset_1(k6_waybel_0(sK1,X0_56),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(k6_waybel_0(sK1,X0_56))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(k6_waybel_0(sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_1167,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_1795,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1732,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | v1_xboole_0(X1_56)
    | k6_domain_1(X1_56,X0_56) = k1_tarski(X0_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1688,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | m1_subset_1(k1_tarski(X0_56),k1_zfmisc_1(X1_56))
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1675,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_318])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_21,c_50])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_1154,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | m1_subset_1(k6_waybel_0(sK1,X0_56),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_1217,plain,
    ( m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_318])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_468,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_21,c_50])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_468])).

cnf(c_1155,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_1214,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(k6_waybel_0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_xboole_0(k6_waybel_0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_23,c_21,c_50,c_68])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | ~ v1_xboole_0(k6_waybel_0(sK1,X0_56)) ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_xboole_0(k6_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_25,c_24,c_21,c_50])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) = k6_waybel_0(sK1,X0_56) ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_16,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_364,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_365,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_47,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_27,c_23,c_21,c_47,c_50,c_68])).

cnf(c_370,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_1158,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_56),sK1)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_1205,plain,
    ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1162,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,X0_56),sK1,sK1)
    | ~ m1_subset_1(X0_56,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1197,plain,
    ( v5_pre_topc(k4_waybel_1(sK1,sK2),sK1,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1190,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1178,plain,
    ( X0_56 != X1_56
    | k6_waybel_0(X0_57,X0_56) = k6_waybel_0(X0_57,X1_56) ),
    theory(equality)).

cnf(c_1188,plain,
    ( k6_waybel_0(sK1,sK2) = k6_waybel_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4178,c_3880,c_2572,c_1961,c_1837,c_1795,c_1732,c_1688,c_1675,c_1217,c_1214,c_1211,c_1208,c_1205,c_1197,c_1190,c_1188,c_47,c_18,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.78/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.78/0.99  
% 1.78/0.99  ------  iProver source info
% 1.78/0.99  
% 1.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.78/0.99  git: non_committed_changes: false
% 1.78/0.99  git: last_make_outside_of_git: false
% 1.78/0.99  
% 1.78/0.99  ------ 
% 1.78/0.99  
% 1.78/0.99  ------ Input Options
% 1.78/0.99  
% 1.78/0.99  --out_options                           all
% 1.78/0.99  --tptp_safe_out                         true
% 1.78/0.99  --problem_path                          ""
% 1.78/0.99  --include_path                          ""
% 1.78/0.99  --clausifier                            res/vclausify_rel
% 1.78/0.99  --clausifier_options                    --mode clausify
% 1.78/0.99  --stdin                                 false
% 1.78/0.99  --stats_out                             all
% 1.78/0.99  
% 1.78/0.99  ------ General Options
% 1.78/0.99  
% 1.78/0.99  --fof                                   false
% 1.78/0.99  --time_out_real                         305.
% 1.78/0.99  --time_out_virtual                      -1.
% 1.78/0.99  --symbol_type_check                     false
% 1.78/0.99  --clausify_out                          false
% 1.78/0.99  --sig_cnt_out                           false
% 1.78/0.99  --trig_cnt_out                          false
% 1.78/0.99  --trig_cnt_out_tolerance                1.
% 1.78/0.99  --trig_cnt_out_sk_spl                   false
% 1.78/0.99  --abstr_cl_out                          false
% 1.78/0.99  
% 1.78/0.99  ------ Global Options
% 1.78/0.99  
% 1.78/0.99  --schedule                              default
% 1.78/0.99  --add_important_lit                     false
% 1.78/0.99  --prop_solver_per_cl                    1000
% 1.78/0.99  --min_unsat_core                        false
% 1.78/0.99  --soft_assumptions                      false
% 1.78/0.99  --soft_lemma_size                       3
% 1.78/0.99  --prop_impl_unit_size                   0
% 1.78/0.99  --prop_impl_unit                        []
% 1.78/0.99  --share_sel_clauses                     true
% 1.78/0.99  --reset_solvers                         false
% 1.78/0.99  --bc_imp_inh                            [conj_cone]
% 1.78/0.99  --conj_cone_tolerance                   3.
% 1.78/0.99  --extra_neg_conj                        none
% 1.78/0.99  --large_theory_mode                     true
% 1.78/0.99  --prolific_symb_bound                   200
% 1.78/0.99  --lt_threshold                          2000
% 1.78/0.99  --clause_weak_htbl                      true
% 1.78/0.99  --gc_record_bc_elim                     false
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing Options
% 1.78/0.99  
% 1.78/0.99  --preprocessing_flag                    true
% 1.78/0.99  --time_out_prep_mult                    0.1
% 1.78/0.99  --splitting_mode                        input
% 1.78/0.99  --splitting_grd                         true
% 1.78/0.99  --splitting_cvd                         false
% 1.78/0.99  --splitting_cvd_svl                     false
% 1.78/0.99  --splitting_nvd                         32
% 1.78/0.99  --sub_typing                            true
% 1.78/0.99  --prep_gs_sim                           true
% 1.78/0.99  --prep_unflatten                        true
% 1.78/0.99  --prep_res_sim                          true
% 1.78/0.99  --prep_upred                            true
% 1.78/0.99  --prep_sem_filter                       exhaustive
% 1.78/0.99  --prep_sem_filter_out                   false
% 1.78/0.99  --pred_elim                             true
% 1.78/0.99  --res_sim_input                         true
% 1.78/0.99  --eq_ax_congr_red                       true
% 1.78/0.99  --pure_diseq_elim                       true
% 1.78/0.99  --brand_transform                       false
% 1.78/0.99  --non_eq_to_eq                          false
% 1.78/0.99  --prep_def_merge                        true
% 1.78/0.99  --prep_def_merge_prop_impl              false
% 1.78/0.99  --prep_def_merge_mbd                    true
% 1.78/0.99  --prep_def_merge_tr_red                 false
% 1.78/0.99  --prep_def_merge_tr_cl                  false
% 1.78/0.99  --smt_preprocessing                     true
% 1.78/0.99  --smt_ac_axioms                         fast
% 1.78/0.99  --preprocessed_out                      false
% 1.78/0.99  --preprocessed_stats                    false
% 1.78/0.99  
% 1.78/0.99  ------ Abstraction refinement Options
% 1.78/0.99  
% 1.78/0.99  --abstr_ref                             []
% 1.78/0.99  --abstr_ref_prep                        false
% 1.78/0.99  --abstr_ref_until_sat                   false
% 1.78/0.99  --abstr_ref_sig_restrict                funpre
% 1.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/0.99  --abstr_ref_under                       []
% 1.78/0.99  
% 1.78/0.99  ------ SAT Options
% 1.78/0.99  
% 1.78/0.99  --sat_mode                              false
% 1.78/0.99  --sat_fm_restart_options                ""
% 1.78/0.99  --sat_gr_def                            false
% 1.78/0.99  --sat_epr_types                         true
% 1.78/0.99  --sat_non_cyclic_types                  false
% 1.78/0.99  --sat_finite_models                     false
% 1.78/0.99  --sat_fm_lemmas                         false
% 1.78/0.99  --sat_fm_prep                           false
% 1.78/0.99  --sat_fm_uc_incr                        true
% 1.78/0.99  --sat_out_model                         small
% 1.78/0.99  --sat_out_clauses                       false
% 1.78/0.99  
% 1.78/0.99  ------ QBF Options
% 1.78/0.99  
% 1.78/0.99  --qbf_mode                              false
% 1.78/0.99  --qbf_elim_univ                         false
% 1.78/0.99  --qbf_dom_inst                          none
% 1.78/0.99  --qbf_dom_pre_inst                      false
% 1.78/0.99  --qbf_sk_in                             false
% 1.78/0.99  --qbf_pred_elim                         true
% 1.78/0.99  --qbf_split                             512
% 1.78/0.99  
% 1.78/0.99  ------ BMC1 Options
% 1.78/0.99  
% 1.78/0.99  --bmc1_incremental                      false
% 1.78/0.99  --bmc1_axioms                           reachable_all
% 1.78/0.99  --bmc1_min_bound                        0
% 1.78/0.99  --bmc1_max_bound                        -1
% 1.78/0.99  --bmc1_max_bound_default                -1
% 1.78/0.99  --bmc1_symbol_reachability              true
% 1.78/0.99  --bmc1_property_lemmas                  false
% 1.78/0.99  --bmc1_k_induction                      false
% 1.78/0.99  --bmc1_non_equiv_states                 false
% 1.78/0.99  --bmc1_deadlock                         false
% 1.78/0.99  --bmc1_ucm                              false
% 1.78/0.99  --bmc1_add_unsat_core                   none
% 1.78/0.99  --bmc1_unsat_core_children              false
% 1.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/0.99  --bmc1_out_stat                         full
% 1.78/0.99  --bmc1_ground_init                      false
% 1.78/0.99  --bmc1_pre_inst_next_state              false
% 1.78/0.99  --bmc1_pre_inst_state                   false
% 1.78/0.99  --bmc1_pre_inst_reach_state             false
% 1.78/0.99  --bmc1_out_unsat_core                   false
% 1.78/0.99  --bmc1_aig_witness_out                  false
% 1.78/0.99  --bmc1_verbose                          false
% 1.78/0.99  --bmc1_dump_clauses_tptp                false
% 1.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.78/0.99  --bmc1_dump_file                        -
% 1.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.78/0.99  --bmc1_ucm_extend_mode                  1
% 1.78/0.99  --bmc1_ucm_init_mode                    2
% 1.78/0.99  --bmc1_ucm_cone_mode                    none
% 1.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.78/0.99  --bmc1_ucm_relax_model                  4
% 1.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/0.99  --bmc1_ucm_layered_model                none
% 1.78/0.99  --bmc1_ucm_max_lemma_size               10
% 1.78/0.99  
% 1.78/0.99  ------ AIG Options
% 1.78/0.99  
% 1.78/0.99  --aig_mode                              false
% 1.78/0.99  
% 1.78/0.99  ------ Instantiation Options
% 1.78/0.99  
% 1.78/0.99  --instantiation_flag                    true
% 1.78/0.99  --inst_sos_flag                         false
% 1.78/0.99  --inst_sos_phase                        true
% 1.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel_side                     num_symb
% 1.78/0.99  --inst_solver_per_active                1400
% 1.78/0.99  --inst_solver_calls_frac                1.
% 1.78/0.99  --inst_passive_queue_type               priority_queues
% 1.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/0.99  --inst_passive_queues_freq              [25;2]
% 1.78/0.99  --inst_dismatching                      true
% 1.78/0.99  --inst_eager_unprocessed_to_passive     true
% 1.78/0.99  --inst_prop_sim_given                   true
% 1.78/0.99  --inst_prop_sim_new                     false
% 1.78/0.99  --inst_subs_new                         false
% 1.78/0.99  --inst_eq_res_simp                      false
% 1.78/0.99  --inst_subs_given                       false
% 1.78/0.99  --inst_orphan_elimination               true
% 1.78/0.99  --inst_learning_loop_flag               true
% 1.78/0.99  --inst_learning_start                   3000
% 1.78/0.99  --inst_learning_factor                  2
% 1.78/0.99  --inst_start_prop_sim_after_learn       3
% 1.78/0.99  --inst_sel_renew                        solver
% 1.78/0.99  --inst_lit_activity_flag                true
% 1.78/0.99  --inst_restr_to_given                   false
% 1.78/0.99  --inst_activity_threshold               500
% 1.78/0.99  --inst_out_proof                        true
% 1.78/0.99  
% 1.78/0.99  ------ Resolution Options
% 1.78/0.99  
% 1.78/0.99  --resolution_flag                       true
% 1.78/0.99  --res_lit_sel                           adaptive
% 1.78/0.99  --res_lit_sel_side                      none
% 1.78/0.99  --res_ordering                          kbo
% 1.78/0.99  --res_to_prop_solver                    active
% 1.78/0.99  --res_prop_simpl_new                    false
% 1.78/0.99  --res_prop_simpl_given                  true
% 1.78/0.99  --res_passive_queue_type                priority_queues
% 1.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/0.99  --res_passive_queues_freq               [15;5]
% 1.78/0.99  --res_forward_subs                      full
% 1.78/0.99  --res_backward_subs                     full
% 1.78/0.99  --res_forward_subs_resolution           true
% 1.78/0.99  --res_backward_subs_resolution          true
% 1.78/0.99  --res_orphan_elimination                true
% 1.78/0.99  --res_time_limit                        2.
% 1.78/0.99  --res_out_proof                         true
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Options
% 1.78/0.99  
% 1.78/0.99  --superposition_flag                    true
% 1.78/0.99  --sup_passive_queue_type                priority_queues
% 1.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.78/0.99  --demod_completeness_check              fast
% 1.78/0.99  --demod_use_ground                      true
% 1.78/0.99  --sup_to_prop_solver                    passive
% 1.78/0.99  --sup_prop_simpl_new                    true
% 1.78/0.99  --sup_prop_simpl_given                  true
% 1.78/0.99  --sup_fun_splitting                     false
% 1.78/0.99  --sup_smt_interval                      50000
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Simplification Setup
% 1.78/0.99  
% 1.78/0.99  --sup_indices_passive                   []
% 1.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_full_bw                           [BwDemod]
% 1.78/0.99  --sup_immed_triv                        [TrivRules]
% 1.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_immed_bw_main                     []
% 1.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  
% 1.78/0.99  ------ Combination Options
% 1.78/0.99  
% 1.78/0.99  --comb_res_mult                         3
% 1.78/0.99  --comb_sup_mult                         2
% 1.78/0.99  --comb_inst_mult                        10
% 1.78/0.99  
% 1.78/0.99  ------ Debug Options
% 1.78/0.99  
% 1.78/0.99  --dbg_backtrace                         false
% 1.78/0.99  --dbg_dump_prop_clauses                 false
% 1.78/0.99  --dbg_dump_prop_clauses_file            -
% 1.78/0.99  --dbg_out_stat                          false
% 1.78/0.99  ------ Parsing...
% 1.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.78/0.99  ------ Proving...
% 1.78/0.99  ------ Problem Properties 
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  clauses                                 16
% 1.78/0.99  conjectures                             3
% 1.78/0.99  EPR                                     1
% 1.78/0.99  Horn                                    12
% 1.78/0.99  unary                                   3
% 1.78/0.99  binary                                  6
% 1.78/0.99  lits                                    58
% 1.78/0.99  lits eq                                 10
% 1.78/0.99  fd_pure                                 0
% 1.78/0.99  fd_pseudo                               0
% 1.78/0.99  fd_cond                                 0
% 1.78/0.99  fd_pseudo_cond                          0
% 1.78/0.99  AC symbols                              0
% 1.78/0.99  
% 1.78/0.99  ------ Schedule dynamic 5 is on 
% 1.78/0.99  
% 1.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  ------ 
% 1.78/0.99  Current options:
% 1.78/0.99  ------ 
% 1.78/0.99  
% 1.78/0.99  ------ Input Options
% 1.78/0.99  
% 1.78/0.99  --out_options                           all
% 1.78/0.99  --tptp_safe_out                         true
% 1.78/0.99  --problem_path                          ""
% 1.78/0.99  --include_path                          ""
% 1.78/0.99  --clausifier                            res/vclausify_rel
% 1.78/0.99  --clausifier_options                    --mode clausify
% 1.78/0.99  --stdin                                 false
% 1.78/0.99  --stats_out                             all
% 1.78/0.99  
% 1.78/0.99  ------ General Options
% 1.78/0.99  
% 1.78/0.99  --fof                                   false
% 1.78/0.99  --time_out_real                         305.
% 1.78/0.99  --time_out_virtual                      -1.
% 1.78/0.99  --symbol_type_check                     false
% 1.78/0.99  --clausify_out                          false
% 1.78/0.99  --sig_cnt_out                           false
% 1.78/0.99  --trig_cnt_out                          false
% 1.78/0.99  --trig_cnt_out_tolerance                1.
% 1.78/0.99  --trig_cnt_out_sk_spl                   false
% 1.78/0.99  --abstr_cl_out                          false
% 1.78/0.99  
% 1.78/0.99  ------ Global Options
% 1.78/0.99  
% 1.78/0.99  --schedule                              default
% 1.78/0.99  --add_important_lit                     false
% 1.78/0.99  --prop_solver_per_cl                    1000
% 1.78/0.99  --min_unsat_core                        false
% 1.78/0.99  --soft_assumptions                      false
% 1.78/0.99  --soft_lemma_size                       3
% 1.78/0.99  --prop_impl_unit_size                   0
% 1.78/0.99  --prop_impl_unit                        []
% 1.78/0.99  --share_sel_clauses                     true
% 1.78/0.99  --reset_solvers                         false
% 1.78/0.99  --bc_imp_inh                            [conj_cone]
% 1.78/0.99  --conj_cone_tolerance                   3.
% 1.78/0.99  --extra_neg_conj                        none
% 1.78/0.99  --large_theory_mode                     true
% 1.78/0.99  --prolific_symb_bound                   200
% 1.78/0.99  --lt_threshold                          2000
% 1.78/0.99  --clause_weak_htbl                      true
% 1.78/0.99  --gc_record_bc_elim                     false
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing Options
% 1.78/0.99  
% 1.78/0.99  --preprocessing_flag                    true
% 1.78/0.99  --time_out_prep_mult                    0.1
% 1.78/0.99  --splitting_mode                        input
% 1.78/0.99  --splitting_grd                         true
% 1.78/0.99  --splitting_cvd                         false
% 1.78/0.99  --splitting_cvd_svl                     false
% 1.78/0.99  --splitting_nvd                         32
% 1.78/0.99  --sub_typing                            true
% 1.78/0.99  --prep_gs_sim                           true
% 1.78/0.99  --prep_unflatten                        true
% 1.78/0.99  --prep_res_sim                          true
% 1.78/0.99  --prep_upred                            true
% 1.78/0.99  --prep_sem_filter                       exhaustive
% 1.78/0.99  --prep_sem_filter_out                   false
% 1.78/0.99  --pred_elim                             true
% 1.78/0.99  --res_sim_input                         true
% 1.78/0.99  --eq_ax_congr_red                       true
% 1.78/0.99  --pure_diseq_elim                       true
% 1.78/0.99  --brand_transform                       false
% 1.78/0.99  --non_eq_to_eq                          false
% 1.78/0.99  --prep_def_merge                        true
% 1.78/0.99  --prep_def_merge_prop_impl              false
% 1.78/0.99  --prep_def_merge_mbd                    true
% 1.78/0.99  --prep_def_merge_tr_red                 false
% 1.78/0.99  --prep_def_merge_tr_cl                  false
% 1.78/0.99  --smt_preprocessing                     true
% 1.78/0.99  --smt_ac_axioms                         fast
% 1.78/0.99  --preprocessed_out                      false
% 1.78/0.99  --preprocessed_stats                    false
% 1.78/0.99  
% 1.78/0.99  ------ Abstraction refinement Options
% 1.78/0.99  
% 1.78/0.99  --abstr_ref                             []
% 1.78/0.99  --abstr_ref_prep                        false
% 1.78/0.99  --abstr_ref_until_sat                   false
% 1.78/0.99  --abstr_ref_sig_restrict                funpre
% 1.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/0.99  --abstr_ref_under                       []
% 1.78/0.99  
% 1.78/0.99  ------ SAT Options
% 1.78/0.99  
% 1.78/0.99  --sat_mode                              false
% 1.78/0.99  --sat_fm_restart_options                ""
% 1.78/0.99  --sat_gr_def                            false
% 1.78/0.99  --sat_epr_types                         true
% 1.78/0.99  --sat_non_cyclic_types                  false
% 1.78/0.99  --sat_finite_models                     false
% 1.78/0.99  --sat_fm_lemmas                         false
% 1.78/0.99  --sat_fm_prep                           false
% 1.78/0.99  --sat_fm_uc_incr                        true
% 1.78/0.99  --sat_out_model                         small
% 1.78/0.99  --sat_out_clauses                       false
% 1.78/0.99  
% 1.78/0.99  ------ QBF Options
% 1.78/0.99  
% 1.78/0.99  --qbf_mode                              false
% 1.78/0.99  --qbf_elim_univ                         false
% 1.78/0.99  --qbf_dom_inst                          none
% 1.78/0.99  --qbf_dom_pre_inst                      false
% 1.78/0.99  --qbf_sk_in                             false
% 1.78/0.99  --qbf_pred_elim                         true
% 1.78/0.99  --qbf_split                             512
% 1.78/0.99  
% 1.78/0.99  ------ BMC1 Options
% 1.78/0.99  
% 1.78/0.99  --bmc1_incremental                      false
% 1.78/0.99  --bmc1_axioms                           reachable_all
% 1.78/0.99  --bmc1_min_bound                        0
% 1.78/0.99  --bmc1_max_bound                        -1
% 1.78/0.99  --bmc1_max_bound_default                -1
% 1.78/0.99  --bmc1_symbol_reachability              true
% 1.78/0.99  --bmc1_property_lemmas                  false
% 1.78/0.99  --bmc1_k_induction                      false
% 1.78/0.99  --bmc1_non_equiv_states                 false
% 1.78/0.99  --bmc1_deadlock                         false
% 1.78/0.99  --bmc1_ucm                              false
% 1.78/0.99  --bmc1_add_unsat_core                   none
% 1.78/0.99  --bmc1_unsat_core_children              false
% 1.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/0.99  --bmc1_out_stat                         full
% 1.78/0.99  --bmc1_ground_init                      false
% 1.78/0.99  --bmc1_pre_inst_next_state              false
% 1.78/0.99  --bmc1_pre_inst_state                   false
% 1.78/0.99  --bmc1_pre_inst_reach_state             false
% 1.78/0.99  --bmc1_out_unsat_core                   false
% 1.78/0.99  --bmc1_aig_witness_out                  false
% 1.78/0.99  --bmc1_verbose                          false
% 1.78/0.99  --bmc1_dump_clauses_tptp                false
% 1.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.78/0.99  --bmc1_dump_file                        -
% 1.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.78/0.99  --bmc1_ucm_extend_mode                  1
% 1.78/0.99  --bmc1_ucm_init_mode                    2
% 1.78/0.99  --bmc1_ucm_cone_mode                    none
% 1.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.78/0.99  --bmc1_ucm_relax_model                  4
% 1.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/0.99  --bmc1_ucm_layered_model                none
% 1.78/0.99  --bmc1_ucm_max_lemma_size               10
% 1.78/0.99  
% 1.78/0.99  ------ AIG Options
% 1.78/0.99  
% 1.78/0.99  --aig_mode                              false
% 1.78/0.99  
% 1.78/0.99  ------ Instantiation Options
% 1.78/0.99  
% 1.78/0.99  --instantiation_flag                    true
% 1.78/0.99  --inst_sos_flag                         false
% 1.78/0.99  --inst_sos_phase                        true
% 1.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel_side                     none
% 1.78/0.99  --inst_solver_per_active                1400
% 1.78/0.99  --inst_solver_calls_frac                1.
% 1.78/0.99  --inst_passive_queue_type               priority_queues
% 1.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/0.99  --inst_passive_queues_freq              [25;2]
% 1.78/0.99  --inst_dismatching                      true
% 1.78/0.99  --inst_eager_unprocessed_to_passive     true
% 1.78/0.99  --inst_prop_sim_given                   true
% 1.78/0.99  --inst_prop_sim_new                     false
% 1.78/0.99  --inst_subs_new                         false
% 1.78/0.99  --inst_eq_res_simp                      false
% 1.78/0.99  --inst_subs_given                       false
% 1.78/0.99  --inst_orphan_elimination               true
% 1.78/0.99  --inst_learning_loop_flag               true
% 1.78/0.99  --inst_learning_start                   3000
% 1.78/0.99  --inst_learning_factor                  2
% 1.78/0.99  --inst_start_prop_sim_after_learn       3
% 1.78/0.99  --inst_sel_renew                        solver
% 1.78/0.99  --inst_lit_activity_flag                true
% 1.78/0.99  --inst_restr_to_given                   false
% 1.78/0.99  --inst_activity_threshold               500
% 1.78/0.99  --inst_out_proof                        true
% 1.78/0.99  
% 1.78/0.99  ------ Resolution Options
% 1.78/0.99  
% 1.78/0.99  --resolution_flag                       false
% 1.78/0.99  --res_lit_sel                           adaptive
% 1.78/0.99  --res_lit_sel_side                      none
% 1.78/0.99  --res_ordering                          kbo
% 1.78/0.99  --res_to_prop_solver                    active
% 1.78/0.99  --res_prop_simpl_new                    false
% 1.78/0.99  --res_prop_simpl_given                  true
% 1.78/0.99  --res_passive_queue_type                priority_queues
% 1.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/0.99  --res_passive_queues_freq               [15;5]
% 1.78/0.99  --res_forward_subs                      full
% 1.78/0.99  --res_backward_subs                     full
% 1.78/0.99  --res_forward_subs_resolution           true
% 1.78/0.99  --res_backward_subs_resolution          true
% 1.78/0.99  --res_orphan_elimination                true
% 1.78/0.99  --res_time_limit                        2.
% 1.78/0.99  --res_out_proof                         true
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Options
% 1.78/0.99  
% 1.78/0.99  --superposition_flag                    true
% 1.78/0.99  --sup_passive_queue_type                priority_queues
% 1.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.78/0.99  --demod_completeness_check              fast
% 1.78/0.99  --demod_use_ground                      true
% 1.78/0.99  --sup_to_prop_solver                    passive
% 1.78/0.99  --sup_prop_simpl_new                    true
% 1.78/0.99  --sup_prop_simpl_given                  true
% 1.78/0.99  --sup_fun_splitting                     false
% 1.78/0.99  --sup_smt_interval                      50000
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Simplification Setup
% 1.78/0.99  
% 1.78/0.99  --sup_indices_passive                   []
% 1.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_full_bw                           [BwDemod]
% 1.78/0.99  --sup_immed_triv                        [TrivRules]
% 1.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_immed_bw_main                     []
% 1.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  
% 1.78/0.99  ------ Combination Options
% 1.78/0.99  
% 1.78/0.99  --comb_res_mult                         3
% 1.78/0.99  --comb_sup_mult                         2
% 1.78/0.99  --comb_inst_mult                        10
% 1.78/0.99  
% 1.78/0.99  ------ Debug Options
% 1.78/0.99  
% 1.78/0.99  --dbg_backtrace                         false
% 1.78/0.99  --dbg_dump_prop_clauses                 false
% 1.78/0.99  --dbg_dump_prop_clauses_file            -
% 1.78/0.99  --dbg_out_stat                          false
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  ------ Proving...
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  % SZS status Theorem for theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  fof(f4,axiom,(
% 1.78/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f21,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.99    inference(ennf_transformation,[],[f4])).
% 1.78/0.99  
% 1.78/0.99  fof(f22,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.99    inference(flattening,[],[f21])).
% 1.78/0.99  
% 1.78/0.99  fof(f40,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.99    inference(nnf_transformation,[],[f22])).
% 1.78/0.99  
% 1.78/0.99  fof(f41,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.99    inference(rectify,[],[f40])).
% 1.78/0.99  
% 1.78/0.99  fof(f42,plain,(
% 1.78/0.99    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.78/0.99    introduced(choice_axiom,[])).
% 1.78/0.99  
% 1.78/0.99  fof(f43,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 1.78/0.99  
% 1.78/0.99  fof(f50,plain,(
% 1.78/0.99    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f43])).
% 1.78/0.99  
% 1.78/0.99  fof(f9,axiom,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f31,plain,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f9])).
% 1.78/0.99  
% 1.78/0.99  fof(f32,plain,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.78/0.99    inference(flattening,[],[f31])).
% 1.78/0.99  
% 1.78/0.99  fof(f59,plain,(
% 1.78/0.99    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f32])).
% 1.78/0.99  
% 1.78/0.99  fof(f6,axiom,(
% 1.78/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f25,plain,(
% 1.78/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.78/0.99    inference(ennf_transformation,[],[f6])).
% 1.78/0.99  
% 1.78/0.99  fof(f26,plain,(
% 1.78/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.78/0.99    inference(flattening,[],[f25])).
% 1.78/0.99  
% 1.78/0.99  fof(f55,plain,(
% 1.78/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f26])).
% 1.78/0.99  
% 1.78/0.99  fof(f13,conjecture,(
% 1.78/0.99    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f14,negated_conjecture,(
% 1.78/0.99    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.78/0.99    inference(negated_conjecture,[],[f13])).
% 1.78/0.99  
% 1.78/0.99  fof(f15,plain,(
% 1.78/0.99    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) => v4_pre_topc(k6_waybel_0(X0,X1),X0))))),
% 1.78/0.99    inference(pure_predicate_removal,[],[f14])).
% 1.78/0.99  
% 1.78/0.99  fof(f38,plain,(
% 1.78/0.99    ? [X0] : (? [X1] : ((~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f15])).
% 1.78/0.99  
% 1.78/0.99  fof(f39,plain,(
% 1.78/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.78/0.99    inference(flattening,[],[f38])).
% 1.78/0.99  
% 1.78/0.99  fof(f45,plain,(
% 1.78/0.99    ( ! [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k6_waybel_0(X0,sK2),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.78/0.99    introduced(choice_axiom,[])).
% 1.78/0.99  
% 1.78/0.99  fof(f44,plain,(
% 1.78/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k6_waybel_0(X0,X1),X0) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k6_waybel_0(sK1,X1),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.78/0.99    introduced(choice_axiom,[])).
% 1.78/0.99  
% 1.78/0.99  fof(f46,plain,(
% 1.78/0.99    (~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f45,f44])).
% 1.78/0.99  
% 1.78/0.99  fof(f69,plain,(
% 1.78/0.99    v1_lattice3(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f71,plain,(
% 1.78/0.99    l1_waybel_9(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f10,axiom,(
% 1.78/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f33,plain,(
% 1.78/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.78/0.99    inference(ennf_transformation,[],[f10])).
% 1.78/0.99  
% 1.78/0.99  fof(f62,plain,(
% 1.78/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f33])).
% 1.78/0.99  
% 1.78/0.99  fof(f58,plain,(
% 1.78/0.99    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f32])).
% 1.78/0.99  
% 1.78/0.99  fof(f2,axiom,(
% 1.78/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f18,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.78/0.99    inference(ennf_transformation,[],[f2])).
% 1.78/0.99  
% 1.78/0.99  fof(f48,plain,(
% 1.78/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f18])).
% 1.78/0.99  
% 1.78/0.99  fof(f5,axiom,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f23,plain,(
% 1.78/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f5])).
% 1.78/0.99  
% 1.78/0.99  fof(f24,plain,(
% 1.78/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.78/0.99    inference(flattening,[],[f23])).
% 1.78/0.99  
% 1.78/0.99  fof(f54,plain,(
% 1.78/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f24])).
% 1.78/0.99  
% 1.78/0.99  fof(f3,axiom,(
% 1.78/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f19,plain,(
% 1.78/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.78/0.99    inference(ennf_transformation,[],[f3])).
% 1.78/0.99  
% 1.78/0.99  fof(f20,plain,(
% 1.78/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.78/0.99    inference(flattening,[],[f19])).
% 1.78/0.99  
% 1.78/0.99  fof(f49,plain,(
% 1.78/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f20])).
% 1.78/0.99  
% 1.78/0.99  fof(f1,axiom,(
% 1.78/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f17,plain,(
% 1.78/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.78/0.99    inference(ennf_transformation,[],[f1])).
% 1.78/0.99  
% 1.78/0.99  fof(f47,plain,(
% 1.78/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f17])).
% 1.78/0.99  
% 1.78/0.99  fof(f7,axiom,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f27,plain,(
% 1.78/0.99    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f7])).
% 1.78/0.99  
% 1.78/0.99  fof(f28,plain,(
% 1.78/0.99    ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.78/0.99    inference(flattening,[],[f27])).
% 1.78/0.99  
% 1.78/0.99  fof(f56,plain,(
% 1.78/0.99    ( ! [X0,X1] : (m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f28])).
% 1.78/0.99  
% 1.78/0.99  fof(f60,plain,(
% 1.78/0.99    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f32])).
% 1.78/0.99  
% 1.78/0.99  fof(f8,axiom,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v2_waybel_0(k6_waybel_0(X0,X1),X0) & ~v1_xboole_0(k6_waybel_0(X0,X1))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f16,plain,(
% 1.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k6_waybel_0(X0,X1)))),
% 1.78/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.78/0.99  
% 1.78/0.99  fof(f29,plain,(
% 1.78/0.99    ! [X0,X1] : (~v1_xboole_0(k6_waybel_0(X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f16])).
% 1.78/0.99  
% 1.78/0.99  fof(f30,plain,(
% 1.78/0.99    ! [X0,X1] : (~v1_xboole_0(k6_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.78/0.99    inference(flattening,[],[f29])).
% 1.78/0.99  
% 1.78/0.99  fof(f57,plain,(
% 1.78/0.99    ( ! [X0,X1] : (~v1_xboole_0(k6_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f30])).
% 1.78/0.99  
% 1.78/0.99  fof(f67,plain,(
% 1.78/0.99    v3_orders_2(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f12,axiom,(
% 1.78/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1)))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f36,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f12])).
% 1.78/0.99  
% 1.78/0.99  fof(f37,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.78/0.99    inference(flattening,[],[f36])).
% 1.78/0.99  
% 1.78/0.99  fof(f64,plain,(
% 1.78/0.99    ( ! [X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),k6_domain_1(u1_struct_0(X0),X1)) = k6_waybel_0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f37])).
% 1.78/0.99  
% 1.78/0.99  fof(f70,plain,(
% 1.78/0.99    v2_lattice3(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f68,plain,(
% 1.78/0.99    v5_orders_2(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f11,axiom,(
% 1.78/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v8_pre_topc(X0) => v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/0.99  
% 1.78/0.99  fof(f34,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.99    inference(ennf_transformation,[],[f11])).
% 1.78/0.99  
% 1.78/0.99  fof(f35,plain,(
% 1.78/0.99    ! [X0] : (! [X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.99    inference(flattening,[],[f34])).
% 1.78/0.99  
% 1.78/0.99  fof(f63,plain,(
% 1.78/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f35])).
% 1.78/0.99  
% 1.78/0.99  fof(f66,plain,(
% 1.78/0.99    v8_pre_topc(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f65,plain,(
% 1.78/0.99    v2_pre_topc(sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f61,plain,(
% 1.78/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.78/0.99    inference(cnf_transformation,[],[f33])).
% 1.78/0.99  
% 1.78/0.99  fof(f73,plain,(
% 1.78/0.99    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f74,plain,(
% 1.78/0.99    ~v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  fof(f72,plain,(
% 1.78/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.78/0.99    inference(cnf_transformation,[],[f46])).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1175,plain,
% 1.78/0.99      ( ~ v4_pre_topc(X0_56,X0_57)
% 1.78/0.99      | v4_pre_topc(X1_56,X0_57)
% 1.78/0.99      | X1_56 != X0_56 ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2007,plain,
% 1.78/0.99      ( v4_pre_topc(X0_56,X0_57)
% 1.78/0.99      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X1_56),k6_domain_1(u1_struct_0(sK1),X2_56)),X0_57)
% 1.78/0.99      | X0_56 != k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X1_56),k6_domain_1(u1_struct_0(sK1),X2_56)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1175]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_4176,plain,
% 1.78/0.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)),sK1)
% 1.78/0.99      | v4_pre_topc(k6_waybel_0(sK1,X1_56),sK1)
% 1.78/0.99      | k6_waybel_0(sK1,X1_56) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2007]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_4178,plain,
% 1.78/0.99      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)),sK1)
% 1.78/0.99      | v4_pre_topc(k6_waybel_0(sK1,sK2),sK1)
% 1.78/0.99      | k6_waybel_0(sK1,sK2) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_4176]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1168,plain,
% 1.78/0.99      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2213,plain,
% 1.78/0.99      ( X0_56 != X1_56
% 1.78/0.99      | k6_waybel_0(sK1,X2_56) != X1_56
% 1.78/0.99      | k6_waybel_0(sK1,X2_56) = X0_56 ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1168]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2539,plain,
% 1.78/0.99      ( X0_56 != k6_waybel_0(sK1,X1_56)
% 1.78/0.99      | k6_waybel_0(sK1,X2_56) = X0_56
% 1.78/0.99      | k6_waybel_0(sK1,X2_56) != k6_waybel_0(sK1,X1_56) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2213]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3879,plain,
% 1.78/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) != k6_waybel_0(sK1,X0_56)
% 1.78/0.99      | k6_waybel_0(sK1,X1_56) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56))
% 1.78/0.99      | k6_waybel_0(sK1,X1_56) != k6_waybel_0(sK1,X0_56) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2539]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_3880,plain,
% 1.78/0.99      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) != k6_waybel_0(sK1,sK2)
% 1.78/0.99      | k6_waybel_0(sK1,sK2) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2))
% 1.78/0.99      | k6_waybel_0(sK1,sK2) != k6_waybel_0(sK1,sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_3879]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1170,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,X1_56)
% 1.78/0.99      | m1_subset_1(X2_56,X3_56)
% 1.78/0.99      | X2_56 != X0_56
% 1.78/0.99      | X3_56 != X1_56 ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2041,plain,
% 1.78/0.99      ( m1_subset_1(X0_56,X1_56)
% 1.78/0.99      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | X1_56 != k1_zfmisc_1(u1_struct_0(sK1))
% 1.78/0.99      | X0_56 != k1_tarski(sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1170]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2253,plain,
% 1.78/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),X0_56)
% 1.78/0.99      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | X0_56 != k1_zfmisc_1(u1_struct_0(sK1))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2041]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2572,plain,
% 1.78/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != k1_tarski(sK2)
% 1.78/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_2253]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_6,plain,
% 1.78/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.78/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 1.78/0.99      | ~ v4_pre_topc(X3,X2)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/0.99      | ~ l1_pre_topc(X2)
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | ~ v1_funct_1(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_12,plain,
% 1.78/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.99      | ~ l1_orders_2(X0)
% 1.78/0.99      | v2_struct_0(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_8,plain,
% 1.78/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_23,negated_conjecture,
% 1.78/0.99      ( v1_lattice3(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_315,plain,
% 1.78/0.99      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK1 != X0 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_316,plain,
% 1.78/0.99      ( ~ l1_orders_2(sK1) | ~ v2_struct_0(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_21,negated_conjecture,
% 1.78/0.99      ( l1_waybel_9(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_14,plain,
% 1.78/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_50,plain,
% 1.78/0.99      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_68,plain,
% 1.78/0.99      ( ~ l1_orders_2(sK1) | ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_318,plain,
% 1.78/0.99      ( ~ v2_struct_0(sK1) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_316,c_23,c_21,c_50,c_68]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_427,plain,
% 1.78/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.99      | ~ l1_orders_2(X0)
% 1.78/0.99      | sK1 != X0 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_318]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_428,plain,
% 1.78/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ l1_orders_2(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_432,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_428,c_21,c_50]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_433,plain,
% 1.78/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_432]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_511,plain,
% 1.78/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 1.78/0.99      | ~ v4_pre_topc(X3,X2)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 1.78/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X2)
% 1.78/0.99      | ~ v1_funct_1(X0)
% 1.78/0.99      | k4_waybel_1(sK1,X4) != X0
% 1.78/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_433]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_512,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.78/0.99      | ~ v4_pre_topc(X3,X2)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X2)
% 1.78/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 1.78/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_13,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 1.78/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_445,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v1_funct_1(k4_waybel_1(X1,X0))
% 1.78/0.99      | sK1 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_318]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_446,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ l1_orders_2(sK1)
% 1.78/0.99      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_516,plain,
% 1.78/0.99      ( ~ l1_pre_topc(X2)
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.78/0.99      | ~ v4_pre_topc(X3,X2)
% 1.78/0.99      | ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.78/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_512,c_21,c_50,c_446]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_517,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0),X1,X2)
% 1.78/0.99      | ~ v4_pre_topc(X3,X2)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k4_waybel_1(sK1,X0),X3),X1)
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.78/0.99      | ~ l1_pre_topc(X1)
% 1.78/0.99      | ~ l1_pre_topc(X2)
% 1.78/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_516]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1153,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,X1_57)
% 1.78/0.99      | ~ v4_pre_topc(X1_56,X1_57)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),k4_waybel_1(sK1,X0_56),X1_56),X0_57)
% 1.78/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(X1_57)))
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 1.78/0.99      | ~ l1_pre_topc(X1_57)
% 1.78/0.99      | ~ l1_pre_topc(X0_57)
% 1.78/0.99      | u1_struct_0(X1_57) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(X0_57) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_517]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1733,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,sK1)
% 1.78/0.99      | ~ v4_pre_topc(X1_56,sK1)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),X1_56),X0_57)
% 1.78/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK1))))
% 1.78/0.99      | ~ l1_pre_topc(X0_57)
% 1.78/0.99      | ~ l1_pre_topc(sK1)
% 1.78/0.99      | u1_struct_0(X0_57) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1153]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1959,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,X0_56),X0_57,sK1)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X1_56)),X0_57)
% 1.78/0.99      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X1_56),sK1)
% 1.78/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK1))))
% 1.78/0.99      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X1_56),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ l1_pre_topc(X0_57)
% 1.78/0.99      | ~ l1_pre_topc(sK1)
% 1.78/0.99      | u1_struct_0(X0_57) != u1_struct_0(sK1)
% 1.78/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1733]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1961,plain,
% 1.78/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK1,sK2),sK1,sK1)
% 1.78/0.99      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)),sK1)
% 1.78/0.99      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1)
% 1.78/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.78/0.99      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.78/0.99      | ~ l1_pre_topc(sK1)
% 1.78/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1959]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.78/0.99      | ~ v1_xboole_0(X1)
% 1.78/0.99      | v1_xboole_0(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1165,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 1.78/0.99      | ~ v1_xboole_0(X1_56)
% 1.78/0.99      | v1_xboole_0(X0_56) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1737,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | v1_xboole_0(X0_56)
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1165]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1835,plain,
% 1.78/0.99      ( ~ m1_subset_1(k6_waybel_0(sK1,X0_56),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | v1_xboole_0(k6_waybel_0(sK1,X0_56))
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1737]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1837,plain,
% 1.78/0.99      ( ~ m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | v1_xboole_0(k6_waybel_0(sK1,sK2))
% 1.78/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1835]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1167,plain,( X0_56 = X0_56 ),theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1795,plain,
% 1.78/0.99      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1732,plain,
% 1.78/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_7,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,X1)
% 1.78/0.99      | v1_xboole_0(X1)
% 1.78/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1164,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,X1_56)
% 1.78/0.99      | v1_xboole_0(X1_56)
% 1.78/0.99      | k6_domain_1(X1_56,X0_56) = k1_tarski(X0_56) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1688,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 1.78/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) = k1_tarski(sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_2,plain,
% 1.78/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_0,plain,
% 1.78/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
% 1.78/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_346,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,X1)
% 1.78/0.99      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 1.78/0.99      | v1_xboole_0(X1) ),
% 1.78/0.99      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1159,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,X1_56)
% 1.78/0.99      | m1_subset_1(k1_tarski(X0_56),k1_zfmisc_1(X1_56))
% 1.78/0.99      | v1_xboole_0(X1_56) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_346]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1675,plain,
% 1.78/0.99      ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.78/0.99      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1159]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_9,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v2_struct_0(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_481,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | m1_subset_1(k6_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | sK1 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_318]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_482,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ l1_orders_2(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_481]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_486,plain,
% 1.78/0.99      ( m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_482,c_21,c_50]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_487,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k6_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_486]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1154,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k6_waybel_0(sK1,X0_56),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_487]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1217,plain,
% 1.78/0.99      ( m1_subset_1(k6_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_11,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v2_struct_0(X1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_463,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | sK1 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_318]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_464,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.78/0.99      | ~ l1_orders_2(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_463]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_468,plain,
% 1.78/0.99      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_464,c_21,c_50]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_469,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_468]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1155,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_469]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1214,plain,
% 1.78/0.99      ( m1_subset_1(k4_waybel_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1155]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_10,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ v3_orders_2(X1)
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(X1,X0)) ),
% 1.78/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_25,negated_conjecture,
% 1.78/0.99      ( v3_orders_2(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_406,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | v2_struct_0(X1)
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(X1,X0))
% 1.78/0.99      | sK1 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_407,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ l1_orders_2(sK1)
% 1.78/0.99      | v2_struct_0(sK1)
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(sK1,X0)) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_411,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(sK1,X0)) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_407,c_23,c_21,c_50,c_68]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1156,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(sK1,X0_56)) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_411]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1211,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.78/0.99      | ~ v1_xboole_0(k6_waybel_0(sK1,sK2)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1156]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_17,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ v5_orders_2(X1)
% 1.78/0.99      | ~ v2_lattice3(X1)
% 1.78/0.99      | ~ v3_orders_2(X1)
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_22,negated_conjecture,
% 1.78/0.99      ( v2_lattice3(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_385,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.78/0.99      | ~ v5_orders_2(X1)
% 1.78/0.99      | ~ v3_orders_2(X1)
% 1.78/0.99      | ~ l1_orders_2(X1)
% 1.78/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X0),k6_domain_1(u1_struct_0(X1),X0)) = k6_waybel_0(X1,X0)
% 1.78/0.99      | sK1 != X1 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_386,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ v5_orders_2(sK1)
% 1.78/0.99      | ~ v3_orders_2(sK1)
% 1.78/0.99      | ~ l1_orders_2(sK1)
% 1.78/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_24,negated_conjecture,
% 1.78/0.99      ( v5_orders_2(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_390,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),k6_domain_1(u1_struct_0(sK1),X0)) = k6_waybel_0(sK1,X0) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_386,c_25,c_24,c_21,c_50]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1157,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0_56,u1_struct_0(sK1))
% 1.78/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_56),k6_domain_1(u1_struct_0(sK1),X0_56)) = k6_waybel_0(sK1,X0_56) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_390]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1208,plain,
% 1.78/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.78/0.99      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK2),k6_domain_1(u1_struct_0(sK1),sK2)) = k6_waybel_0(sK1,sK2) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1157]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_16,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.99      | ~ v2_pre_topc(X0)
% 1.78/0.99      | ~ v8_pre_topc(X0)
% 1.78/0.99      | v2_struct_0(X0)
% 1.78/0.99      | ~ l1_pre_topc(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_26,negated_conjecture,
% 1.78/0.99      ( v8_pre_topc(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_364,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(X0),X1),X0)
% 1.78/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/0.99      | ~ v2_pre_topc(X0)
% 1.78/0.99      | v2_struct_0(X0)
% 1.78/0.99      | ~ l1_pre_topc(X0)
% 1.78/0.99      | sK1 != X0 ),
% 1.78/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_365,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | ~ v2_pre_topc(sK1)
% 1.78/0.99      | v2_struct_0(sK1)
% 1.78/0.99      | ~ l1_pre_topc(sK1) ),
% 1.78/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_27,negated_conjecture,
% 1.78/0.99      ( v2_pre_topc(sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_15,plain,
% 1.78/0.99      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.78/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_47,plain,
% 1.78/0.99      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_369,plain,
% 1.78/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.78/0.99      | v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1) ),
% 1.78/0.99      inference(global_propositional_subsumption,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_365,c_27,c_23,c_21,c_47,c_50,c_68]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_370,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0),sK1)
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(renaming,[status(thm)],[c_369]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1158,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),X0_56),sK1)
% 1.78/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_370]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1205,plain,
% 1.78/0.99      ( v4_pre_topc(k6_domain_1(u1_struct_0(sK1),sK2),sK1)
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1158]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_19,negated_conjecture,
% 1.78/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0),sK1,sK1)
% 1.78/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1162,negated_conjecture,
% 1.78/0.99      ( v5_pre_topc(k4_waybel_1(sK1,X0_56),sK1,sK1)
% 1.78/0.99      | ~ m1_subset_1(X0_56,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1197,plain,
% 1.78/0.99      ( v5_pre_topc(k4_waybel_1(sK1,sK2),sK1,sK1)
% 1.78/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1162]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1190,plain,
% 1.78/0.99      ( sK2 = sK2 ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1178,plain,
% 1.78/0.99      ( X0_56 != X1_56
% 1.78/0.99      | k6_waybel_0(X0_57,X0_56) = k6_waybel_0(X0_57,X1_56) ),
% 1.78/0.99      theory(equality) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_1188,plain,
% 1.78/0.99      ( k6_waybel_0(sK1,sK2) = k6_waybel_0(sK1,sK2) | sK2 != sK2 ),
% 1.78/0.99      inference(instantiation,[status(thm)],[c_1178]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_18,negated_conjecture,
% 1.78/0.99      ( ~ v4_pre_topc(k6_waybel_0(sK1,sK2),sK1) ),
% 1.78/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(c_20,negated_conjecture,
% 1.78/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.78/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.78/0.99  
% 1.78/0.99  cnf(contradiction,plain,
% 1.78/0.99      ( $false ),
% 1.78/0.99      inference(minisat,
% 1.78/0.99                [status(thm)],
% 1.78/0.99                [c_4178,c_3880,c_2572,c_1961,c_1837,c_1795,c_1732,c_1688,
% 1.78/0.99                 c_1675,c_1217,c_1214,c_1211,c_1208,c_1205,c_1197,c_1190,
% 1.78/0.99                 c_1188,c_47,c_18,c_20,c_21]) ).
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  ------                               Statistics
% 1.78/0.99  
% 1.78/0.99  ------ General
% 1.78/0.99  
% 1.78/0.99  abstr_ref_over_cycles:                  0
% 1.78/0.99  abstr_ref_under_cycles:                 0
% 1.78/0.99  gc_basic_clause_elim:                   0
% 1.78/0.99  forced_gc_time:                         0
% 1.78/0.99  parsing_time:                           0.007
% 1.78/0.99  unif_index_cands_time:                  0.
% 1.78/0.99  unif_index_add_time:                    0.
% 1.78/0.99  orderings_time:                         0.
% 1.78/0.99  out_proof_time:                         0.009
% 1.78/0.99  total_time:                             0.168
% 1.78/0.99  num_of_symbols:                         61
% 1.78/0.99  num_of_terms:                           3519
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing
% 1.78/0.99  
% 1.78/0.99  num_of_splits:                          0
% 1.78/0.99  num_of_split_atoms:                     0
% 1.78/0.99  num_of_reused_defs:                     0
% 1.78/0.99  num_eq_ax_congr_red:                    28
% 1.78/0.99  num_of_sem_filtered_clauses:            1
% 1.78/0.99  num_of_subtypes:                        2
% 1.78/0.99  monotx_restored_types:                  0
% 1.78/0.99  sat_num_of_epr_types:                   0
% 1.78/0.99  sat_num_of_non_cyclic_types:            0
% 1.78/0.99  sat_guarded_non_collapsed_types:        0
% 1.78/0.99  num_pure_diseq_elim:                    0
% 1.78/0.99  simp_replaced_by:                       0
% 1.78/0.99  res_preprocessed:                       101
% 1.78/0.99  prep_upred:                             0
% 1.78/0.99  prep_unflattend:                        18
% 1.78/0.99  smt_new_axioms:                         0
% 1.78/0.99  pred_elim_cands:                        5
% 1.78/0.99  pred_elim:                              12
% 1.78/0.99  pred_elim_cl:                           12
% 1.78/0.99  pred_elim_cycles:                       14
% 1.78/0.99  merged_defs:                            0
% 1.78/0.99  merged_defs_ncl:                        0
% 1.78/0.99  bin_hyper_res:                          0
% 1.78/0.99  prep_cycles:                            4
% 1.78/0.99  pred_elim_time:                         0.017
% 1.78/0.99  splitting_time:                         0.
% 1.78/0.99  sem_filter_time:                        0.
% 1.78/0.99  monotx_time:                            0.
% 1.78/0.99  subtype_inf_time:                       0.
% 1.78/0.99  
% 1.78/0.99  ------ Problem properties
% 1.78/0.99  
% 1.78/0.99  clauses:                                16
% 1.78/0.99  conjectures:                            3
% 1.78/0.99  epr:                                    1
% 1.78/0.99  horn:                                   12
% 1.78/0.99  ground:                                 3
% 1.78/0.99  unary:                                  3
% 1.78/0.99  binary:                                 6
% 1.78/0.99  lits:                                   58
% 1.78/0.99  lits_eq:                                10
% 1.78/0.99  fd_pure:                                0
% 1.78/0.99  fd_pseudo:                              0
% 1.78/0.99  fd_cond:                                0
% 1.78/0.99  fd_pseudo_cond:                         0
% 1.78/0.99  ac_symbols:                             0
% 1.78/0.99  
% 1.78/0.99  ------ Propositional Solver
% 1.78/0.99  
% 1.78/0.99  prop_solver_calls:                      28
% 1.78/0.99  prop_fast_solver_calls:                 1161
% 1.78/0.99  smt_solver_calls:                       0
% 1.78/0.99  smt_fast_solver_calls:                  0
% 1.78/0.99  prop_num_of_clauses:                    1097
% 1.78/0.99  prop_preprocess_simplified:             4652
% 1.78/0.99  prop_fo_subsumed:                       33
% 1.78/0.99  prop_solver_time:                       0.
% 1.78/0.99  smt_solver_time:                        0.
% 1.78/0.99  smt_fast_solver_time:                   0.
% 1.78/0.99  prop_fast_solver_time:                  0.
% 1.78/0.99  prop_unsat_core_time:                   0.
% 1.78/0.99  
% 1.78/0.99  ------ QBF
% 1.78/0.99  
% 1.78/0.99  qbf_q_res:                              0
% 1.78/0.99  qbf_num_tautologies:                    0
% 1.78/0.99  qbf_prep_cycles:                        0
% 1.78/0.99  
% 1.78/0.99  ------ BMC1
% 1.78/0.99  
% 1.78/0.99  bmc1_current_bound:                     -1
% 1.78/0.99  bmc1_last_solved_bound:                 -1
% 1.78/0.99  bmc1_unsat_core_size:                   -1
% 1.78/0.99  bmc1_unsat_core_parents_size:           -1
% 1.78/0.99  bmc1_merge_next_fun:                    0
% 1.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.78/0.99  
% 1.78/0.99  ------ Instantiation
% 1.78/0.99  
% 1.78/0.99  inst_num_of_clauses:                    372
% 1.78/0.99  inst_num_in_passive:                    110
% 1.78/0.99  inst_num_in_active:                     256
% 1.78/0.99  inst_num_in_unprocessed:                5
% 1.78/0.99  inst_num_of_loops:                      272
% 1.78/0.99  inst_num_of_learning_restarts:          0
% 1.78/0.99  inst_num_moves_active_passive:          10
% 1.78/0.99  inst_lit_activity:                      0
% 1.78/0.99  inst_lit_activity_moves:                0
% 1.78/0.99  inst_num_tautologies:                   0
% 1.78/0.99  inst_num_prop_implied:                  0
% 1.78/0.99  inst_num_existing_simplified:           0
% 1.78/0.99  inst_num_eq_res_simplified:             0
% 1.78/0.99  inst_num_child_elim:                    0
% 1.78/0.99  inst_num_of_dismatching_blockings:      121
% 1.78/0.99  inst_num_of_non_proper_insts:           477
% 1.78/0.99  inst_num_of_duplicates:                 0
% 1.78/0.99  inst_inst_num_from_inst_to_res:         0
% 1.78/0.99  inst_dismatching_checking_time:         0.
% 1.78/0.99  
% 1.78/0.99  ------ Resolution
% 1.78/0.99  
% 1.78/0.99  res_num_of_clauses:                     0
% 1.78/0.99  res_num_in_passive:                     0
% 1.78/0.99  res_num_in_active:                      0
% 1.78/0.99  res_num_of_loops:                       105
% 1.78/0.99  res_forward_subset_subsumed:            86
% 1.78/0.99  res_backward_subset_subsumed:           2
% 1.78/0.99  res_forward_subsumed:                   0
% 1.78/0.99  res_backward_subsumed:                  0
% 1.78/0.99  res_forward_subsumption_resolution:     1
% 1.78/0.99  res_backward_subsumption_resolution:    0
% 1.78/0.99  res_clause_to_clause_subsumption:       391
% 1.78/0.99  res_orphan_elimination:                 0
% 1.78/0.99  res_tautology_del:                      136
% 1.78/0.99  res_num_eq_res_simplified:              0
% 1.78/0.99  res_num_sel_changes:                    0
% 1.78/0.99  res_moves_from_active_to_pass:          0
% 1.78/0.99  
% 1.78/0.99  ------ Superposition
% 1.78/0.99  
% 1.78/0.99  sup_time_total:                         0.
% 1.78/0.99  sup_time_generating:                    0.
% 1.78/0.99  sup_time_sim_full:                      0.
% 1.78/0.99  sup_time_sim_immed:                     0.
% 1.78/0.99  
% 1.78/0.99  sup_num_of_clauses:                     59
% 1.78/0.99  sup_num_in_active:                      54
% 1.78/0.99  sup_num_in_passive:                     5
% 1.78/0.99  sup_num_of_loops:                       54
% 1.78/0.99  sup_fw_superposition:                   32
% 1.78/0.99  sup_bw_superposition:                   7
% 1.78/0.99  sup_immediate_simplified:               3
% 1.78/0.99  sup_given_eliminated:                   0
% 1.78/0.99  comparisons_done:                       0
% 1.78/0.99  comparisons_avoided:                    0
% 1.78/0.99  
% 1.78/0.99  ------ Simplifications
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  sim_fw_subset_subsumed:                 1
% 1.78/0.99  sim_bw_subset_subsumed:                 0
% 1.78/0.99  sim_fw_subsumed:                        2
% 1.78/0.99  sim_bw_subsumed:                        0
% 1.78/0.99  sim_fw_subsumption_res:                 0
% 1.78/0.99  sim_bw_subsumption_res:                 0
% 1.78/0.99  sim_tautology_del:                      1
% 1.78/0.99  sim_eq_tautology_del:                   0
% 1.78/0.99  sim_eq_res_simp:                        0
% 1.78/0.99  sim_fw_demodulated:                     0
% 1.78/0.99  sim_bw_demodulated:                     0
% 1.78/0.99  sim_light_normalised:                   1
% 1.78/0.99  sim_joinable_taut:                      0
% 1.78/0.99  sim_joinable_simp:                      0
% 1.78/0.99  sim_ac_normalised:                      0
% 1.78/0.99  sim_smt_subsumption:                    0
% 1.78/0.99  
%------------------------------------------------------------------------------
