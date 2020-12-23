%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:53 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  246 (2541 expanded)
%              Number of clauses        :  165 ( 717 expanded)
%              Number of leaves         :   20 ( 739 expanded)
%              Depth                    :   27
%              Number of atoms          : 1137 (23365 expanded)
%              Number of equality atoms :  215 ( 474 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
               => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
            ( ( l1_waybel_0(X1,X0)
              & v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                 => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
          & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1)))
        & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,sK2)),k10_yellow_6(X0,k3_waybel_2(X0,X2,sK2)))
            & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK2,X0)
        & v3_yellow_6(sK2,X0)
        & v7_waybel_0(sK2)
        & v4_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
                & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(sK1,X2,k11_yellow_6(sK1,X1)),k10_yellow_6(sK1,k3_waybel_2(sK1,X2,X1)))
              & v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & l1_waybel_0(X1,sK1)
          & v3_yellow_6(X1,sK1)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & v8_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2)))
    & v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & l1_waybel_0(sK2,sK1)
    & v3_yellow_6(sK2,sK1)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_waybel_9(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & v8_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f47,f46,f45])).

fof(f80,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ? [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ? [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2))
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k4_waybel_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        & v1_funct_2(X2,X0,u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
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
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X0)
               => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
      | ~ v5_pre_topc(X2,X0,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1519,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1816,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_385,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_753,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_754,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_844,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_385,c_754])).

cnf(c_845,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1515,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_845])).

cnf(c_1831,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1816,c_1515])).

cnf(c_22,negated_conjecture,
    ( v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_399,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_waybel_9(X2)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_5])).

cnf(c_400,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_32,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_716,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_400,c_32])).

cnf(c_717,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_60,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_93,plain,
    ( ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_721,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v3_yellow_6(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_33,c_28,c_26,c_60,c_93])).

cnf(c_722,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_762,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_722])).

cnf(c_763,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,negated_conjecture,
    ( v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_765,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_25,c_24,c_23,c_21])).

cnf(c_1517,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_765])).

cnf(c_1818,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1517])).

cnf(c_1834,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1818,c_1515])).

cnf(c_12,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_849,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_754])).

cnf(c_850,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_849])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_850,c_28,c_26,c_60,c_93])).

cnf(c_855,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_854])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_867,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_754])).

cnf(c_868,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_84,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_870,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_28,c_26,c_60,c_84,c_93])).

cnf(c_1097,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | k2_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_870])).

cnf(c_1098,plain,
    ( ~ v1_funct_2(X0,k2_struct_0(sK1),X1)
    | ~ m1_subset_1(X2,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(k2_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X3)))
    | ~ v1_funct_1(X2)
    | k3_funct_2(k2_struct_0(sK1),X3,X2,X1) = k1_funct_1(X2,X1)
    | k4_waybel_1(sK1,X0) != X2
    | u1_struct_0(sK1) != X3
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_855,c_1098])).

cnf(c_1228,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_96,plain,
    ( ~ l1_orders_2(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_99,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_754])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_1232,plain,
    ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_28,c_26,c_60,c_93,c_96,c_99,c_906])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
    inference(renaming,[status(thm)],[c_1232])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
    inference(subtyping,[status(esa)],[c_1233])).

cnf(c_1826,plain,
    ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1508])).

cnf(c_1893,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1826,c_1515])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_754])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_932,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_28,c_26,c_60,c_93])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_932])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_1821,plain,
    ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_1849,plain,
    ( m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1821,c_1515])).

cnf(c_1898,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1893,c_1849])).

cnf(c_3049,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1834,c_1898])).

cnf(c_3345,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1831,c_3049])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_28,c_26,c_60,c_93])).

cnf(c_10,plain,
    ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_878,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_197,c_754])).

cnf(c_879,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_883,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_879,c_28,c_26,c_60,c_93])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_910,c_884])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_933,c_922])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71) ),
    inference(subtyping,[status(esa)],[c_944])).

cnf(c_1822,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_1868,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1822,c_1515])).

cnf(c_2222,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1834,c_1868])).

cnf(c_2886,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1831,c_2222])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_646,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_29,c_26,c_60])).

cnf(c_1518,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_1817,plain,
    ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1861,plain,
    ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1817,c_1515])).

cnf(c_2146,plain,
    ( k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1834,c_1861])).

cnf(c_2724,plain,
    ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1831,c_2146])).

cnf(c_2901,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2886,c_2724])).

cnf(c_3359,plain,
    ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3345,c_2901])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1009,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_754])).

cnf(c_1010,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_28,c_26,c_60,c_93])).

cnf(c_1015,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(renaming,[status(thm)],[c_1014])).

cnf(c_1076,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2)
    | k2_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1015,c_870])).

cnf(c_1077,plain,
    ( ~ v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(k2_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_1076])).

cnf(c_1203,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X2)
    | k2_yellow_6(k2_struct_0(sK1),sK1,X2,X1) = k1_funct_1(X2,X1)
    | k4_waybel_1(sK1,X0) != X2
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_855,c_1077])).

cnf(c_1204,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1208,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_28,c_26,c_60,c_93,c_96,c_99,c_906])).

cnf(c_1209,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
    inference(renaming,[status(thm)],[c_1208])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
    inference(subtyping,[status(esa)],[c_1209])).

cnf(c_1825,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_1884,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1825,c_1515])).

cnf(c_1889,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1884,c_1849])).

cnf(c_2531,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1834,c_1889])).

cnf(c_2958,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1831,c_2531])).

cnf(c_17,plain,
    ( ~ v5_pre_topc(X0,X1,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
    | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v3_orders_2(X1)
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_584,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
    | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v3_orders_2(X1)
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k4_waybel_1(sK1,sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_585,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v3_orders_2(sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(X0)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_31,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_589,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26])).

cnf(c_590,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_773,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_590])).

cnf(c_774,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_776,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_25,c_24,c_23,c_21])).

cnf(c_777,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_1130,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_777,c_855])).

cnf(c_1361,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_1130])).

cnf(c_1507,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_1361])).

cnf(c_1522,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1507])).

cnf(c_1827,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_1902,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1827,c_1515])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1543,plain,
    ( X0_71 != X1_71
    | k4_waybel_1(X0_70,X0_71) = k4_waybel_1(X0_70,X1_71) ),
    theory(equality)).

cnf(c_1558,plain,
    ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1527,plain,
    ( X0_71 = X0_71 ),
    theory(equality)).

cnf(c_1568,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_1514,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0_71)) ),
    inference(subtyping,[status(esa)],[c_910])).

cnf(c_1580,plain,
    ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,X0_71)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1582,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1521,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1507])).

cnf(c_1602,plain,
    ( k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_1604,plain,
    ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_1949,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1849])).

cnf(c_2418,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1902,c_47,c_1558,c_1568,c_1582,c_1604,c_1949,c_1831])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_823,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_28,c_26,c_25,c_60,c_93])).

cnf(c_1516,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2) ),
    inference(subtyping,[status(esa)],[c_828])).

cnf(c_1819,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_1844,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1819,c_1515])).

cnf(c_2018,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1831,c_1844])).

cnf(c_2422,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2418,c_2018])).

cnf(c_2975,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2958,c_2422])).

cnf(c_3363,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3359,c_2975])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3363,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.99  
% 2.67/0.99  ------  iProver source info
% 2.67/0.99  
% 2.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.99  git: non_committed_changes: false
% 2.67/0.99  git: last_make_outside_of_git: false
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  
% 2.67/0.99  ------ Input Options
% 2.67/0.99  
% 2.67/0.99  --out_options                           all
% 2.67/0.99  --tptp_safe_out                         true
% 2.67/0.99  --problem_path                          ""
% 2.67/0.99  --include_path                          ""
% 2.67/0.99  --clausifier                            res/vclausify_rel
% 2.67/0.99  --clausifier_options                    --mode clausify
% 2.67/0.99  --stdin                                 false
% 2.67/0.99  --stats_out                             all
% 2.67/0.99  
% 2.67/0.99  ------ General Options
% 2.67/0.99  
% 2.67/0.99  --fof                                   false
% 2.67/0.99  --time_out_real                         305.
% 2.67/0.99  --time_out_virtual                      -1.
% 2.67/0.99  --symbol_type_check                     false
% 2.67/0.99  --clausify_out                          false
% 2.67/0.99  --sig_cnt_out                           false
% 2.67/0.99  --trig_cnt_out                          false
% 2.67/0.99  --trig_cnt_out_tolerance                1.
% 2.67/0.99  --trig_cnt_out_sk_spl                   false
% 2.67/0.99  --abstr_cl_out                          false
% 2.67/0.99  
% 2.67/0.99  ------ Global Options
% 2.67/0.99  
% 2.67/0.99  --schedule                              default
% 2.67/0.99  --add_important_lit                     false
% 2.67/0.99  --prop_solver_per_cl                    1000
% 2.67/0.99  --min_unsat_core                        false
% 2.67/0.99  --soft_assumptions                      false
% 2.67/0.99  --soft_lemma_size                       3
% 2.67/0.99  --prop_impl_unit_size                   0
% 2.67/0.99  --prop_impl_unit                        []
% 2.67/0.99  --share_sel_clauses                     true
% 2.67/0.99  --reset_solvers                         false
% 2.67/0.99  --bc_imp_inh                            [conj_cone]
% 2.67/0.99  --conj_cone_tolerance                   3.
% 2.67/0.99  --extra_neg_conj                        none
% 2.67/0.99  --large_theory_mode                     true
% 2.67/0.99  --prolific_symb_bound                   200
% 2.67/0.99  --lt_threshold                          2000
% 2.67/0.99  --clause_weak_htbl                      true
% 2.67/0.99  --gc_record_bc_elim                     false
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing Options
% 2.67/0.99  
% 2.67/0.99  --preprocessing_flag                    true
% 2.67/0.99  --time_out_prep_mult                    0.1
% 2.67/0.99  --splitting_mode                        input
% 2.67/0.99  --splitting_grd                         true
% 2.67/0.99  --splitting_cvd                         false
% 2.67/0.99  --splitting_cvd_svl                     false
% 2.67/0.99  --splitting_nvd                         32
% 2.67/0.99  --sub_typing                            true
% 2.67/0.99  --prep_gs_sim                           true
% 2.67/0.99  --prep_unflatten                        true
% 2.67/0.99  --prep_res_sim                          true
% 2.67/0.99  --prep_upred                            true
% 2.67/0.99  --prep_sem_filter                       exhaustive
% 2.67/0.99  --prep_sem_filter_out                   false
% 2.67/0.99  --pred_elim                             true
% 2.67/0.99  --res_sim_input                         true
% 2.67/0.99  --eq_ax_congr_red                       true
% 2.67/0.99  --pure_diseq_elim                       true
% 2.67/0.99  --brand_transform                       false
% 2.67/0.99  --non_eq_to_eq                          false
% 2.67/0.99  --prep_def_merge                        true
% 2.67/0.99  --prep_def_merge_prop_impl              false
% 2.67/0.99  --prep_def_merge_mbd                    true
% 2.67/0.99  --prep_def_merge_tr_red                 false
% 2.67/0.99  --prep_def_merge_tr_cl                  false
% 2.67/0.99  --smt_preprocessing                     true
% 2.67/0.99  --smt_ac_axioms                         fast
% 2.67/0.99  --preprocessed_out                      false
% 2.67/0.99  --preprocessed_stats                    false
% 2.67/0.99  
% 2.67/0.99  ------ Abstraction refinement Options
% 2.67/0.99  
% 2.67/0.99  --abstr_ref                             []
% 2.67/0.99  --abstr_ref_prep                        false
% 2.67/0.99  --abstr_ref_until_sat                   false
% 2.67/0.99  --abstr_ref_sig_restrict                funpre
% 2.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.99  --abstr_ref_under                       []
% 2.67/0.99  
% 2.67/0.99  ------ SAT Options
% 2.67/0.99  
% 2.67/0.99  --sat_mode                              false
% 2.67/0.99  --sat_fm_restart_options                ""
% 2.67/0.99  --sat_gr_def                            false
% 2.67/0.99  --sat_epr_types                         true
% 2.67/0.99  --sat_non_cyclic_types                  false
% 2.67/0.99  --sat_finite_models                     false
% 2.67/0.99  --sat_fm_lemmas                         false
% 2.67/0.99  --sat_fm_prep                           false
% 2.67/0.99  --sat_fm_uc_incr                        true
% 2.67/0.99  --sat_out_model                         small
% 2.67/0.99  --sat_out_clauses                       false
% 2.67/0.99  
% 2.67/0.99  ------ QBF Options
% 2.67/0.99  
% 2.67/0.99  --qbf_mode                              false
% 2.67/0.99  --qbf_elim_univ                         false
% 2.67/0.99  --qbf_dom_inst                          none
% 2.67/0.99  --qbf_dom_pre_inst                      false
% 2.67/0.99  --qbf_sk_in                             false
% 2.67/0.99  --qbf_pred_elim                         true
% 2.67/0.99  --qbf_split                             512
% 2.67/0.99  
% 2.67/0.99  ------ BMC1 Options
% 2.67/0.99  
% 2.67/0.99  --bmc1_incremental                      false
% 2.67/0.99  --bmc1_axioms                           reachable_all
% 2.67/0.99  --bmc1_min_bound                        0
% 2.67/0.99  --bmc1_max_bound                        -1
% 2.67/0.99  --bmc1_max_bound_default                -1
% 2.67/0.99  --bmc1_symbol_reachability              true
% 2.67/0.99  --bmc1_property_lemmas                  false
% 2.67/0.99  --bmc1_k_induction                      false
% 2.67/0.99  --bmc1_non_equiv_states                 false
% 2.67/0.99  --bmc1_deadlock                         false
% 2.67/0.99  --bmc1_ucm                              false
% 2.67/0.99  --bmc1_add_unsat_core                   none
% 2.67/0.99  --bmc1_unsat_core_children              false
% 2.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.99  --bmc1_out_stat                         full
% 2.67/0.99  --bmc1_ground_init                      false
% 2.67/0.99  --bmc1_pre_inst_next_state              false
% 2.67/0.99  --bmc1_pre_inst_state                   false
% 2.67/0.99  --bmc1_pre_inst_reach_state             false
% 2.67/0.99  --bmc1_out_unsat_core                   false
% 2.67/0.99  --bmc1_aig_witness_out                  false
% 2.67/0.99  --bmc1_verbose                          false
% 2.67/0.99  --bmc1_dump_clauses_tptp                false
% 2.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.99  --bmc1_dump_file                        -
% 2.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.99  --bmc1_ucm_extend_mode                  1
% 2.67/0.99  --bmc1_ucm_init_mode                    2
% 2.67/0.99  --bmc1_ucm_cone_mode                    none
% 2.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.99  --bmc1_ucm_relax_model                  4
% 2.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.99  --bmc1_ucm_layered_model                none
% 2.67/0.99  --bmc1_ucm_max_lemma_size               10
% 2.67/0.99  
% 2.67/0.99  ------ AIG Options
% 2.67/0.99  
% 2.67/0.99  --aig_mode                              false
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation Options
% 2.67/0.99  
% 2.67/0.99  --instantiation_flag                    true
% 2.67/0.99  --inst_sos_flag                         false
% 2.67/0.99  --inst_sos_phase                        true
% 2.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel_side                     num_symb
% 2.67/0.99  --inst_solver_per_active                1400
% 2.67/0.99  --inst_solver_calls_frac                1.
% 2.67/0.99  --inst_passive_queue_type               priority_queues
% 2.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.99  --inst_passive_queues_freq              [25;2]
% 2.67/0.99  --inst_dismatching                      true
% 2.67/0.99  --inst_eager_unprocessed_to_passive     true
% 2.67/0.99  --inst_prop_sim_given                   true
% 2.67/0.99  --inst_prop_sim_new                     false
% 2.67/0.99  --inst_subs_new                         false
% 2.67/0.99  --inst_eq_res_simp                      false
% 2.67/0.99  --inst_subs_given                       false
% 2.67/0.99  --inst_orphan_elimination               true
% 2.67/0.99  --inst_learning_loop_flag               true
% 2.67/0.99  --inst_learning_start                   3000
% 2.67/0.99  --inst_learning_factor                  2
% 2.67/0.99  --inst_start_prop_sim_after_learn       3
% 2.67/0.99  --inst_sel_renew                        solver
% 2.67/0.99  --inst_lit_activity_flag                true
% 2.67/0.99  --inst_restr_to_given                   false
% 2.67/0.99  --inst_activity_threshold               500
% 2.67/0.99  --inst_out_proof                        true
% 2.67/0.99  
% 2.67/0.99  ------ Resolution Options
% 2.67/0.99  
% 2.67/0.99  --resolution_flag                       true
% 2.67/0.99  --res_lit_sel                           adaptive
% 2.67/0.99  --res_lit_sel_side                      none
% 2.67/0.99  --res_ordering                          kbo
% 2.67/0.99  --res_to_prop_solver                    active
% 2.67/0.99  --res_prop_simpl_new                    false
% 2.67/0.99  --res_prop_simpl_given                  true
% 2.67/0.99  --res_passive_queue_type                priority_queues
% 2.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.99  --res_passive_queues_freq               [15;5]
% 2.67/0.99  --res_forward_subs                      full
% 2.67/0.99  --res_backward_subs                     full
% 2.67/0.99  --res_forward_subs_resolution           true
% 2.67/0.99  --res_backward_subs_resolution          true
% 2.67/0.99  --res_orphan_elimination                true
% 2.67/0.99  --res_time_limit                        2.
% 2.67/0.99  --res_out_proof                         true
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Options
% 2.67/0.99  
% 2.67/0.99  --superposition_flag                    true
% 2.67/0.99  --sup_passive_queue_type                priority_queues
% 2.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.99  --demod_completeness_check              fast
% 2.67/0.99  --demod_use_ground                      true
% 2.67/0.99  --sup_to_prop_solver                    passive
% 2.67/0.99  --sup_prop_simpl_new                    true
% 2.67/0.99  --sup_prop_simpl_given                  true
% 2.67/0.99  --sup_fun_splitting                     false
% 2.67/0.99  --sup_smt_interval                      50000
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Simplification Setup
% 2.67/0.99  
% 2.67/0.99  --sup_indices_passive                   []
% 2.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_full_bw                           [BwDemod]
% 2.67/0.99  --sup_immed_triv                        [TrivRules]
% 2.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_immed_bw_main                     []
% 2.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  
% 2.67/0.99  ------ Combination Options
% 2.67/0.99  
% 2.67/0.99  --comb_res_mult                         3
% 2.67/0.99  --comb_sup_mult                         2
% 2.67/0.99  --comb_inst_mult                        10
% 2.67/0.99  
% 2.67/0.99  ------ Debug Options
% 2.67/0.99  
% 2.67/0.99  --dbg_backtrace                         false
% 2.67/0.99  --dbg_dump_prop_clauses                 false
% 2.67/0.99  --dbg_dump_prop_clauses_file            -
% 2.67/0.99  --dbg_out_stat                          false
% 2.67/0.99  ------ Parsing...
% 2.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.99  ------ Proving...
% 2.67/0.99  ------ Problem Properties 
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  clauses                                 15
% 2.67/0.99  conjectures                             2
% 2.67/1.00  EPR                                     0
% 2.67/1.00  Horn                                    13
% 2.67/1.00  unary                                   4
% 2.67/1.00  binary                                  3
% 2.67/1.00  lits                                    39
% 2.67/1.00  lits eq                                 10
% 2.67/1.00  fd_pure                                 0
% 2.67/1.00  fd_pseudo                               0
% 2.67/1.00  fd_cond                                 0
% 2.67/1.00  fd_pseudo_cond                          0
% 2.67/1.00  AC symbols                              0
% 2.67/1.00  
% 2.67/1.00  ------ Schedule dynamic 5 is on 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  Current options:
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     none
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       false
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ Proving...
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS status Theorem for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  fof(f14,conjecture,(
% 2.67/1.00    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f15,negated_conjecture,(
% 2.67/1.00    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.67/1.00    inference(negated_conjecture,[],[f14])).
% 2.67/1.00  
% 2.67/1.00  fof(f39,plain,(
% 2.67/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f15])).
% 2.67/1.00  
% 2.67/1.00  fof(f40,plain,(
% 2.67/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.67/1.00    inference(flattening,[],[f39])).
% 2.67/1.00  
% 2.67/1.00  fof(f47,plain,(
% 2.67/1.00    ( ! [X0,X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1))) & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f46,plain,(
% 2.67/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,sK2)),k10_yellow_6(X0,k3_waybel_2(X0,X2,sK2))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2,X0) & v3_yellow_6(sK2,X0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f45,plain,(
% 2.67/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK1,X2,k11_yellow_6(sK1,X1)),k10_yellow_6(sK1,k3_waybel_2(sK1,X2,X1))) & v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(X1,sK1) & v3_yellow_6(X1,sK1) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f48,plain,(
% 2.67/1.00    ((~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) & v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) & m1_subset_1(sK3,u1_struct_0(sK1))) & l1_waybel_0(sK2,sK1) & v3_yellow_6(sK2,sK1) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f47,f46,f45])).
% 2.67/1.00  
% 2.67/1.00  fof(f80,plain,(
% 2.67/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f3,axiom,(
% 2.67/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f19,plain,(
% 2.67/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f3])).
% 2.67/1.00  
% 2.67/1.00  fof(f51,plain,(
% 2.67/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f19])).
% 2.67/1.00  
% 2.67/1.00  fof(f2,axiom,(
% 2.67/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f18,plain,(
% 2.67/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f2])).
% 2.67/1.00  
% 2.67/1.00  fof(f50,plain,(
% 2.67/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f18])).
% 2.67/1.00  
% 2.67/1.00  fof(f11,axiom,(
% 2.67/1.00    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f34,plain,(
% 2.67/1.00    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f11])).
% 2.67/1.00  
% 2.67/1.00  fof(f64,plain,(
% 2.67/1.00    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f34])).
% 2.67/1.00  
% 2.67/1.00  fof(f74,plain,(
% 2.67/1.00    l1_waybel_9(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f78,plain,(
% 2.67/1.00    v3_yellow_6(sK2,sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f63,plain,(
% 2.67/1.00    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f34])).
% 2.67/1.00  
% 2.67/1.00  fof(f6,axiom,(
% 2.67/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f24,plain,(
% 2.67/1.00    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f6])).
% 2.67/1.00  
% 2.67/1.00  fof(f25,plain,(
% 2.67/1.00    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(flattening,[],[f24])).
% 2.67/1.00  
% 2.67/1.00  fof(f54,plain,(
% 2.67/1.00    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f25])).
% 2.67/1.00  
% 2.67/1.00  fof(f68,plain,(
% 2.67/1.00    v8_pre_topc(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f67,plain,(
% 2.67/1.00    v2_pre_topc(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f72,plain,(
% 2.67/1.00    v1_lattice3(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f4,axiom,(
% 2.67/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f20,plain,(
% 2.67/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f4])).
% 2.67/1.00  
% 2.67/1.00  fof(f21,plain,(
% 2.67/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.67/1.00    inference(flattening,[],[f20])).
% 2.67/1.00  
% 2.67/1.00  fof(f52,plain,(
% 2.67/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f21])).
% 2.67/1.00  
% 2.67/1.00  fof(f75,plain,(
% 2.67/1.00    ~v2_struct_0(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f76,plain,(
% 2.67/1.00    v4_orders_2(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f77,plain,(
% 2.67/1.00    v7_waybel_0(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f79,plain,(
% 2.67/1.00    l1_waybel_0(sK2,sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f10,axiom,(
% 2.67/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f32,plain,(
% 2.67/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f10])).
% 2.67/1.00  
% 2.67/1.00  fof(f33,plain,(
% 2.67/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(flattening,[],[f32])).
% 2.67/1.00  
% 2.67/1.00  fof(f61,plain,(
% 2.67/1.00    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f33])).
% 2.67/1.00  
% 2.67/1.00  fof(f1,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f16,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f1])).
% 2.67/1.00  
% 2.67/1.00  fof(f17,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.67/1.00    inference(flattening,[],[f16])).
% 2.67/1.00  
% 2.67/1.00  fof(f49,plain,(
% 2.67/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f17])).
% 2.67/1.00  
% 2.67/1.00  fof(f7,axiom,(
% 2.67/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f26,plain,(
% 2.67/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f7])).
% 2.67/1.00  
% 2.67/1.00  fof(f27,plain,(
% 2.67/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(flattening,[],[f26])).
% 2.67/1.00  
% 2.67/1.00  fof(f55,plain,(
% 2.67/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f27])).
% 2.67/1.00  
% 2.67/1.00  fof(f60,plain,(
% 2.67/1.00    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f33])).
% 2.67/1.00  
% 2.67/1.00  fof(f62,plain,(
% 2.67/1.00    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f33])).
% 2.67/1.00  
% 2.67/1.00  fof(f9,axiom,(
% 2.67/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f30,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f9])).
% 2.67/1.00  
% 2.67/1.00  fof(f31,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(flattening,[],[f30])).
% 2.67/1.00  
% 2.67/1.00  fof(f41,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(nnf_transformation,[],[f31])).
% 2.67/1.00  
% 2.67/1.00  fof(f42,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(rectify,[],[f41])).
% 2.67/1.00  
% 2.67/1.00  fof(f43,plain,(
% 2.67/1.00    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f44,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.67/1.00  
% 2.67/1.00  fof(f57,plain,(
% 2.67/1.00    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f83,plain,(
% 2.67/1.00    ( ! [X4,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(equality_resolution,[],[f57])).
% 2.67/1.00  
% 2.67/1.00  fof(f5,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f22,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f5])).
% 2.67/1.00  
% 2.67/1.00  fof(f23,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.67/1.00    inference(flattening,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  fof(f53,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f23])).
% 2.67/1.00  
% 2.67/1.00  fof(f73,plain,(
% 2.67/1.00    v2_lattice3(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f71,plain,(
% 2.67/1.00    v5_orders_2(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f8,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f28,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f8])).
% 2.67/1.00  
% 2.67/1.00  fof(f29,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 2.67/1.00    inference(flattening,[],[f28])).
% 2.67/1.00  
% 2.67/1.00  fof(f56,plain,(
% 2.67/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f29])).
% 2.67/1.00  
% 2.67/1.00  fof(f13,axiom,(
% 2.67/1.00    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f37,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f13])).
% 2.67/1.00  
% 2.67/1.00  fof(f38,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.67/1.00    inference(flattening,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  fof(f66,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f38])).
% 2.67/1.00  
% 2.67/1.00  fof(f81,plain,(
% 2.67/1.00    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f69,plain,(
% 2.67/1.00    v3_orders_2(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f70,plain,(
% 2.67/1.00    v4_orders_2(sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  fof(f12,axiom,(
% 2.67/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f35,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f12])).
% 2.67/1.00  
% 2.67/1.00  fof(f36,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.67/1.00    inference(flattening,[],[f35])).
% 2.67/1.00  
% 2.67/1.00  fof(f65,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f36])).
% 2.67/1.00  
% 2.67/1.00  fof(f82,plain,(
% 2.67/1.00    ~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2)))),
% 2.67/1.00    inference(cnf_transformation,[],[f48])).
% 2.67/1.00  
% 2.67/1.00  cnf(c_20,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1519,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1816,plain,
% 2.67/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2,plain,
% 2.67/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1,plain,
% 2.67/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_385,plain,
% 2.67/1.00      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/1.00      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_14,plain,
% 2.67/1.00      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_26,negated_conjecture,
% 2.67/1.00      ( l1_waybel_9(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_753,plain,
% 2.67/1.00      ( l1_orders_2(X0) | sK1 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_754,plain,
% 2.67/1.00      ( l1_orders_2(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_753]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_844,plain,
% 2.67/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_385,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_845,plain,
% 2.67/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_844]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1515,plain,
% 2.67/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_845]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1831,plain,
% 2.67/1.00      ( m1_subset_1(sK3,k2_struct_0(sK1)) = iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1816,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_22,negated_conjecture,
% 2.67/1.00      ( v3_yellow_6(sK2,sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_15,plain,
% 2.67/1.00      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_5,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,X1)
% 2.67/1.00      | ~ l1_waybel_0(X0,X1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v8_pre_topc(X1)
% 2.67/1.00      | ~ l1_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | v2_struct_0(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_399,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,X1)
% 2.67/1.00      | ~ l1_waybel_0(X0,X1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.67/1.00      | ~ l1_waybel_9(X2)
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v8_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | X1 != X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_5]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_400,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,X1)
% 2.67/1.00      | ~ l1_waybel_0(X0,X1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.67/1.00      | ~ l1_waybel_9(X1)
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v8_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | v2_struct_0(X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_32,negated_conjecture,
% 2.67/1.00      ( v8_pre_topc(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_716,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,X1)
% 2.67/1.00      | ~ l1_waybel_0(X0,X1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.67/1.00      | ~ l1_waybel_9(X1)
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_400,c_32]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_717,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,sK1)
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.67/1.00      | ~ l1_waybel_9(sK1)
% 2.67/1.00      | ~ v2_pre_topc(sK1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | v2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_716]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_33,negated_conjecture,
% 2.67/1.00      ( v2_pre_topc(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_28,negated_conjecture,
% 2.67/1.00      ( v1_lattice3(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_60,plain,
% 2.67/1.00      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3,plain,
% 2.67/1.00      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_93,plain,
% 2.67/1.00      ( ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) | ~ l1_orders_2(sK1) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_721,plain,
% 2.67/1.00      ( v2_struct_0(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | ~ v3_yellow_6(X0,sK1) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_717,c_33,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_722,plain,
% 2.67/1.00      ( ~ v3_yellow_6(X0,sK1)
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_721]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_762,plain,
% 2.67/1.00      ( ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | sK2 != X0
% 2.67/1.00      | sK1 != sK1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_722]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_763,plain,
% 2.67/1.00      ( ~ l1_waybel_0(sK2,sK1)
% 2.67/1.00      | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
% 2.67/1.00      | ~ v4_orders_2(sK2)
% 2.67/1.00      | ~ v7_waybel_0(sK2)
% 2.67/1.00      | v2_struct_0(sK2) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_762]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_25,negated_conjecture,
% 2.67/1.00      ( ~ v2_struct_0(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_24,negated_conjecture,
% 2.67/1.00      ( v4_orders_2(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_23,negated_conjecture,
% 2.67/1.00      ( v7_waybel_0(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_21,negated_conjecture,
% 2.67/1.00      ( l1_waybel_0(sK2,sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_765,plain,
% 2.67/1.00      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_763,c_25,c_24,c_23,c_21]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1517,plain,
% 2.67/1.00      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_765]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1818,plain,
% 2.67/1.00      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1517]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1834,plain,
% 2.67/1.00      ( m1_subset_1(k11_yellow_6(sK1,sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1818,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_12,plain,
% 2.67/1.00      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ l1_orders_2(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_849,plain,
% 2.67/1.00      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | sK1 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_850,plain,
% 2.67/1.00      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | v2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_849]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_854,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_850,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_855,plain,
% 2.67/1.00      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_854]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_0,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | ~ m1_subset_1(X3,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.67/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6,plain,
% 2.67/1.00      ( v2_struct_0(X0)
% 2.67/1.00      | ~ l1_orders_2(X0)
% 2.67/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_867,plain,
% 2.67/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_868,plain,
% 2.67/1.00      ( v2_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_867]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_84,plain,
% 2.67/1.00      ( v2_struct_0(sK1)
% 2.67/1.00      | ~ l1_orders_2(sK1)
% 2.67/1.00      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_870,plain,
% 2.67/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_868,c_28,c_26,c_60,c_84,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1097,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | ~ m1_subset_1(X3,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.67/1.00      | k2_struct_0(sK1) != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_870]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1098,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,k2_struct_0(sK1),X1)
% 2.67/1.00      | ~ m1_subset_1(X2,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k3_funct_2(k2_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_1097]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1227,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X3)))
% 2.67/1.00      | ~ v1_funct_1(X2)
% 2.67/1.00      | k3_funct_2(k2_struct_0(sK1),X3,X2,X1) = k1_funct_1(X2,X1)
% 2.67/1.00      | k4_waybel_1(sK1,X0) != X2
% 2.67/1.00      | u1_struct_0(sK1) != X3
% 2.67/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_855,c_1098]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1228,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.67/1.00      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 2.67/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_1227]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_96,plain,
% 2.67/1.00      ( ~ l1_orders_2(sK1) | l1_struct_0(sK1) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_99,plain,
% 2.67/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_13,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_905,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | v1_funct_1(k4_waybel_1(X1,X0))
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_906,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | v2_struct_0(sK1)
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_905]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1232,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1228,c_28,c_26,c_60,c_93,c_96,c_99,c_906]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1233,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_1232]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1508,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_1233]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1826,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1508]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1893,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1826,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_11,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | ~ l1_orders_2(X1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_927,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_928,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | v2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_927]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_932,plain,
% 2.67/1.00      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_928,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_933,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_932]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1513,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_933]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1821,plain,
% 2.67/1.00      ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1849,plain,
% 2.67/1.00      ( m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1821,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1898,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(forward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1893,c_1849]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3049,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1834,c_1898]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3345,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1831,c_3049]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_910,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_906,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_10,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ l1_orders_2(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.67/1.00      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_196,plain,
% 2.67/1.00      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ l1_orders_2(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.67/1.00      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_10,c_12]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_197,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.67/1.00      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_196]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_878,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.67/1.00      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_197,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_879,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | v2_struct_0(sK1)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_878]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_883,plain,
% 2.67/1.00      ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_879,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_884,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_883]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_922,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(backward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_910,c_884]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_944,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(backward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_933,c_922]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1512,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
% 2.67/1.00      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_944]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1822,plain,
% 2.67/1.00      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1868,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1822,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2222,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1834,c_1868]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2886,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1831,c_2222]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_4,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/1.00      | ~ v5_orders_2(X1)
% 2.67/1.00      | ~ v2_lattice3(X1)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_27,negated_conjecture,
% 2.67/1.00      ( v2_lattice3(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_646,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/1.00      | ~ v5_orders_2(X1)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_647,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ v5_orders_2(sK1)
% 2.67/1.00      | ~ l1_orders_2(sK1)
% 2.67/1.00      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_646]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_29,negated_conjecture,
% 2.67/1.00      ( v5_orders_2(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_651,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.67/1.00      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_647,c_29,c_26,c_60]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1518,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
% 2.67/1.00      | k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_651]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1817,plain,
% 2.67/1.00      ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1861,plain,
% 2.67/1.00      ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1817,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2146,plain,
% 2.67/1.00      ( k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1834,c_1861]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2724,plain,
% 2.67/1.00      ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1831,c_2146]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2901,plain,
% 2.67/1.00      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_2886,c_2724]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3359,plain,
% 2.67/1.00      ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_3345,c_2901]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_7,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.67/1.00      | ~ m1_subset_1(X3,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.67/1.00      | v2_struct_0(X2)
% 2.67/1.00      | ~ l1_orders_2(X2)
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.67/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1009,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.67/1.00      | ~ m1_subset_1(X3,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.67/1.00      | v2_struct_0(X2)
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.67/1.00      | sK1 != X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_754]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1010,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.00      | v2_struct_0(sK1)
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_1009]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1014,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.00      | ~ m1_subset_1(X2,X1)
% 2.67/1.00      | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1010,c_28,c_26,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1015,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.00      | v1_xboole_0(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_1014]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1076,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2)
% 2.67/1.00      | k2_struct_0(sK1) != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_1015,c_870]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1077,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k2_yellow_6(k2_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_1076]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1203,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(X2)
% 2.67/1.00      | k2_yellow_6(k2_struct_0(sK1),sK1,X2,X1) = k1_funct_1(X2,X1)
% 2.67/1.00      | k4_waybel_1(sK1,X0) != X2
% 2.67/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.67/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_855,c_1077]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1204,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.67/1.00      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 2.67/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_1203]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1208,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1204,c_28,c_26,c_60,c_93,c_96,c_99,c_906]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1209,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_1208]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1509,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_1209]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1825,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1884,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1825,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1889,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 2.67/1.00      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(forward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1884,c_1849]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2531,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1834,c_1889]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2958,plain,
% 2.67/1.00      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1831,c_2531]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_17,plain,
% 2.67/1.00      ( ~ v5_pre_topc(X0,X1,X1)
% 2.67/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.67/1.00      | ~ v3_yellow_6(X2,X1)
% 2.67/1.00      | ~ l1_waybel_0(X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | ~ v3_orders_2(X1)
% 2.67/1.00      | ~ l1_waybel_9(X1)
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v8_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X2)
% 2.67/1.00      | ~ v4_orders_2(X1)
% 2.67/1.00      | ~ v7_waybel_0(X2)
% 2.67/1.00      | ~ v5_orders_2(X1)
% 2.67/1.00      | ~ v2_lattice3(X1)
% 2.67/1.00      | ~ v1_lattice3(X1)
% 2.67/1.00      | v2_struct_0(X2)
% 2.67/1.00      | ~ v1_funct_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_19,negated_conjecture,
% 2.67/1.00      ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_584,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.67/1.00      | ~ v3_yellow_6(X2,X1)
% 2.67/1.00      | ~ l1_waybel_0(X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.67/1.00      | ~ v3_orders_2(X1)
% 2.67/1.00      | ~ l1_waybel_9(X1)
% 2.67/1.00      | ~ v2_pre_topc(X1)
% 2.67/1.00      | ~ v8_pre_topc(X1)
% 2.67/1.00      | ~ v4_orders_2(X1)
% 2.67/1.00      | ~ v4_orders_2(X2)
% 2.67/1.00      | ~ v7_waybel_0(X2)
% 2.67/1.00      | ~ v5_orders_2(X1)
% 2.67/1.00      | ~ v2_lattice3(X1)
% 2.67/1.00      | ~ v1_lattice3(X1)
% 2.67/1.00      | v2_struct_0(X2)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | k4_waybel_1(sK1,sK3) != X0
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_585,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.67/1.00      | ~ v3_yellow_6(X0,sK1)
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v3_orders_2(sK1)
% 2.67/1.00      | ~ l1_waybel_9(sK1)
% 2.67/1.00      | ~ v2_pre_topc(sK1)
% 2.67/1.00      | ~ v8_pre_topc(sK1)
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v4_orders_2(sK1)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | ~ v5_orders_2(sK1)
% 2.67/1.00      | ~ v2_lattice3(sK1)
% 2.67/1.00      | ~ v1_lattice3(sK1)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_31,negated_conjecture,
% 2.67/1.00      ( v3_orders_2(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_30,negated_conjecture,
% 2.67/1.00      ( v4_orders_2(sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_589,plain,
% 2.67/1.00      ( ~ v7_waybel_0(X0)
% 2.67/1.00      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.67/1.00      | ~ v3_yellow_6(X0,sK1)
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_585,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_590,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.67/1.00      | ~ v3_yellow_6(X0,sK1)
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_589]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_773,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.67/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v4_orders_2(X0)
% 2.67/1.00      | ~ v7_waybel_0(X0)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.67/1.00      | sK2 != X0
% 2.67/1.00      | sK1 != sK1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_590]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_774,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ l1_waybel_0(sK2,sK1)
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v4_orders_2(sK2)
% 2.67/1.00      | ~ v7_waybel_0(sK2)
% 2.67/1.00      | v2_struct_0(sK2)
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_773]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_776,plain,
% 2.67/1.00      ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_774,c_25,c_24,c_23,c_21]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_777,plain,
% 2.67/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.67/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_776]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1130,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.67/1.00      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
% 2.67/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_777,c_855]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1361,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.67/1.00      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
% 2.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_1130]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1507,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.67/1.00      | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_1361]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1522,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.67/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.67/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.67/1.00      | sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[])],
% 2.67/1.00                [c_1507]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1827,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1902,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.67/1.00      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1827,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_47,plain,
% 2.67/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1543,plain,
% 2.67/1.00      ( X0_71 != X1_71
% 2.67/1.00      | k4_waybel_1(X0_70,X0_71) = k4_waybel_1(X0_70,X1_71) ),
% 2.67/1.00      theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1558,plain,
% 2.67/1.00      ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3) | sK3 != sK3 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1527,plain,( X0_71 = X0_71 ),theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1568,plain,
% 2.67/1.00      ( sK3 = sK3 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1527]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1514,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,X0_71)) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_910]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1580,plain,
% 2.67/1.00      ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,X0_71)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1582,plain,
% 2.67/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1580]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1521,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
% 2.67/1.00      | ~ sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.67/1.00                [c_1507]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1602,plain,
% 2.67/1.00      ( k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1604,plain,
% 2.67/1.00      ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
% 2.67/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1602]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1949,plain,
% 2.67/1.00      ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
% 2.67/1.00      | m1_subset_1(sK3,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1849]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2418,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1902,c_47,c_1558,c_1568,c_1582,c_1604,c_1949,c_1831]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_16,plain,
% 2.67/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.67/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | v2_struct_0(X0)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_823,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.67/1.00      | v2_struct_0(X2)
% 2.67/1.00      | v2_struct_0(X1)
% 2.67/1.00      | ~ l1_orders_2(X1)
% 2.67/1.00      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
% 2.67/1.00      | sK2 != X2
% 2.67/1.00      | sK1 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_824,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | v2_struct_0(sK2)
% 2.67/1.00      | v2_struct_0(sK1)
% 2.67/1.00      | ~ l1_orders_2(sK1)
% 2.67/1.00      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_823]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_828,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.67/1.00      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_824,c_28,c_26,c_25,c_60,c_93]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1516,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 2.67/1.00      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2) ),
% 2.67/1.00      inference(subtyping,[status(esa)],[c_828]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1819,plain,
% 2.67/1.00      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
% 2.67/1.00      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1844,plain,
% 2.67/1.00      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
% 2.67/1.00      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_1819,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2018,plain,
% 2.67/1.00      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1831,c_1844]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2422,plain,
% 2.67/1.00      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_2418,c_2018]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2975,plain,
% 2.67/1.00      ( r2_hidden(k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_2958,c_2422]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3363,plain,
% 2.67/1.00      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_3359,c_2975]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_18,negated_conjecture,
% 2.67/1.00      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_49,plain,
% 2.67/1.00      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(contradiction,plain,
% 2.67/1.00      ( $false ),
% 2.67/1.00      inference(minisat,[status(thm)],[c_3363,c_49]) ).
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  ------                               Statistics
% 2.67/1.00  
% 2.67/1.00  ------ General
% 2.67/1.00  
% 2.67/1.00  abstr_ref_over_cycles:                  0
% 2.67/1.00  abstr_ref_under_cycles:                 0
% 2.67/1.00  gc_basic_clause_elim:                   0
% 2.67/1.00  forced_gc_time:                         0
% 2.67/1.00  parsing_time:                           0.012
% 2.67/1.00  unif_index_cands_time:                  0.
% 2.67/1.00  unif_index_add_time:                    0.
% 2.67/1.00  orderings_time:                         0.
% 2.67/1.00  out_proof_time:                         0.018
% 2.67/1.00  total_time:                             0.159
% 2.67/1.00  num_of_symbols:                         76
% 2.67/1.00  num_of_terms:                           2905
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing
% 2.67/1.00  
% 2.67/1.00  num_of_splits:                          1
% 2.67/1.00  num_of_split_atoms:                     1
% 2.67/1.00  num_of_reused_defs:                     0
% 2.67/1.00  num_eq_ax_congr_red:                    37
% 2.67/1.00  num_of_sem_filtered_clauses:            4
% 2.67/1.00  num_of_subtypes:                        8
% 2.67/1.00  monotx_restored_types:                  0
% 2.67/1.00  sat_num_of_epr_types:                   0
% 2.67/1.00  sat_num_of_non_cyclic_types:            0
% 2.67/1.00  sat_guarded_non_collapsed_types:        0
% 2.67/1.00  num_pure_diseq_elim:                    0
% 2.67/1.00  simp_replaced_by:                       0
% 2.67/1.00  res_preprocessed:                       126
% 2.67/1.00  prep_upred:                             0
% 2.67/1.00  prep_unflattend:                        29
% 2.67/1.00  smt_new_axioms:                         0
% 2.67/1.00  pred_elim_cands:                        3
% 2.67/1.00  pred_elim:                              18
% 2.67/1.00  pred_elim_cl:                           20
% 2.67/1.00  pred_elim_cycles:                       26
% 2.67/1.00  merged_defs:                            0
% 2.67/1.00  merged_defs_ncl:                        0
% 2.67/1.00  bin_hyper_res:                          0
% 2.67/1.00  prep_cycles:                            4
% 2.67/1.00  pred_elim_time:                         0.03
% 2.67/1.00  splitting_time:                         0.
% 2.67/1.00  sem_filter_time:                        0.
% 2.67/1.00  monotx_time:                            0.
% 2.67/1.00  subtype_inf_time:                       0.
% 2.67/1.00  
% 2.67/1.00  ------ Problem properties
% 2.67/1.00  
% 2.67/1.00  clauses:                                15
% 2.67/1.00  conjectures:                            2
% 2.67/1.00  epr:                                    0
% 2.67/1.00  horn:                                   13
% 2.67/1.00  ground:                                 5
% 2.67/1.00  unary:                                  4
% 2.67/1.00  binary:                                 3
% 2.67/1.00  lits:                                   39
% 2.67/1.00  lits_eq:                                10
% 2.67/1.00  fd_pure:                                0
% 2.67/1.00  fd_pseudo:                              0
% 2.67/1.00  fd_cond:                                0
% 2.67/1.00  fd_pseudo_cond:                         0
% 2.67/1.00  ac_symbols:                             0
% 2.67/1.00  
% 2.67/1.00  ------ Propositional Solver
% 2.67/1.00  
% 2.67/1.00  prop_solver_calls:                      29
% 2.67/1.00  prop_fast_solver_calls:                 1052
% 2.67/1.00  smt_solver_calls:                       0
% 2.67/1.00  smt_fast_solver_calls:                  0
% 2.67/1.00  prop_num_of_clauses:                    873
% 2.67/1.00  prop_preprocess_simplified:             3534
% 2.67/1.00  prop_fo_subsumed:                       48
% 2.67/1.00  prop_solver_time:                       0.
% 2.67/1.00  smt_solver_time:                        0.
% 2.67/1.00  smt_fast_solver_time:                   0.
% 2.67/1.00  prop_fast_solver_time:                  0.
% 2.67/1.00  prop_unsat_core_time:                   0.
% 2.67/1.00  
% 2.67/1.00  ------ QBF
% 2.67/1.00  
% 2.67/1.00  qbf_q_res:                              0
% 2.67/1.00  qbf_num_tautologies:                    0
% 2.67/1.00  qbf_prep_cycles:                        0
% 2.67/1.00  
% 2.67/1.00  ------ BMC1
% 2.67/1.00  
% 2.67/1.00  bmc1_current_bound:                     -1
% 2.67/1.00  bmc1_last_solved_bound:                 -1
% 2.67/1.00  bmc1_unsat_core_size:                   -1
% 2.67/1.00  bmc1_unsat_core_parents_size:           -1
% 2.67/1.00  bmc1_merge_next_fun:                    0
% 2.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation
% 2.67/1.00  
% 2.67/1.00  inst_num_of_clauses:                    246
% 2.67/1.00  inst_num_in_passive:                    39
% 2.67/1.00  inst_num_in_active:                     201
% 2.67/1.00  inst_num_in_unprocessed:                6
% 2.67/1.00  inst_num_of_loops:                      210
% 2.67/1.00  inst_num_of_learning_restarts:          0
% 2.67/1.00  inst_num_moves_active_passive:          2
% 2.67/1.00  inst_lit_activity:                      0
% 2.67/1.00  inst_lit_activity_moves:                0
% 2.67/1.00  inst_num_tautologies:                   0
% 2.67/1.00  inst_num_prop_implied:                  0
% 2.67/1.00  inst_num_existing_simplified:           0
% 2.67/1.00  inst_num_eq_res_simplified:             0
% 2.67/1.00  inst_num_child_elim:                    0
% 2.67/1.00  inst_num_of_dismatching_blockings:      69
% 2.67/1.00  inst_num_of_non_proper_insts:           327
% 2.67/1.00  inst_num_of_duplicates:                 0
% 2.67/1.00  inst_inst_num_from_inst_to_res:         0
% 2.67/1.00  inst_dismatching_checking_time:         0.
% 2.67/1.00  
% 2.67/1.00  ------ Resolution
% 2.67/1.00  
% 2.67/1.00  res_num_of_clauses:                     0
% 2.67/1.00  res_num_in_passive:                     0
% 2.67/1.00  res_num_in_active:                      0
% 2.67/1.00  res_num_of_loops:                       130
% 2.67/1.00  res_forward_subset_subsumed:            96
% 2.67/1.00  res_backward_subset_subsumed:           2
% 2.67/1.00  res_forward_subsumed:                   0
% 2.67/1.00  res_backward_subsumed:                  0
% 2.67/1.00  res_forward_subsumption_resolution:     4
% 2.67/1.00  res_backward_subsumption_resolution:    2
% 2.67/1.00  res_clause_to_clause_subsumption:       161
% 2.67/1.00  res_orphan_elimination:                 0
% 2.67/1.00  res_tautology_del:                      73
% 2.67/1.00  res_num_eq_res_simplified:              1
% 2.67/1.00  res_num_sel_changes:                    0
% 2.67/1.00  res_moves_from_active_to_pass:          0
% 2.67/1.00  
% 2.67/1.00  ------ Superposition
% 2.67/1.00  
% 2.67/1.00  sup_time_total:                         0.
% 2.67/1.00  sup_time_generating:                    0.
% 2.67/1.00  sup_time_sim_full:                      0.
% 2.67/1.00  sup_time_sim_immed:                     0.
% 2.67/1.00  
% 2.67/1.00  sup_num_of_clauses:                     56
% 2.67/1.00  sup_num_in_active:                      37
% 2.67/1.00  sup_num_in_passive:                     19
% 2.67/1.00  sup_num_of_loops:                       41
% 2.67/1.00  sup_fw_superposition:                   36
% 2.67/1.00  sup_bw_superposition:                   6
% 2.67/1.00  sup_immediate_simplified:               6
% 2.67/1.00  sup_given_eliminated:                   0
% 2.67/1.00  comparisons_done:                       0
% 2.67/1.00  comparisons_avoided:                    0
% 2.67/1.00  
% 2.67/1.00  ------ Simplifications
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  sim_fw_subset_subsumed:                 0
% 2.67/1.00  sim_bw_subset_subsumed:                 0
% 2.67/1.00  sim_fw_subsumed:                        0
% 2.67/1.00  sim_bw_subsumed:                        0
% 2.67/1.00  sim_fw_subsumption_res:                 2
% 2.67/1.00  sim_bw_subsumption_res:                 0
% 2.67/1.00  sim_tautology_del:                      0
% 2.67/1.00  sim_eq_tautology_del:                   0
% 2.67/1.00  sim_eq_res_simp:                        0
% 2.67/1.00  sim_fw_demodulated:                     0
% 2.67/1.00  sim_bw_demodulated:                     4
% 2.67/1.00  sim_light_normalised:                   21
% 2.67/1.00  sim_joinable_taut:                      0
% 2.67/1.00  sim_joinable_simp:                      0
% 2.67/1.00  sim_ac_normalised:                      0
% 2.67/1.00  sim_smt_subsumption:                    0
% 2.67/1.00  
%------------------------------------------------------------------------------
