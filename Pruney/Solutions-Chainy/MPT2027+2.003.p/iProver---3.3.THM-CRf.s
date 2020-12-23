%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:53 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  248 (2532 expanded)
%              Number of clauses        :  167 ( 702 expanded)
%              Number of leaves         :   20 ( 741 expanded)
%              Depth                    :   27
%              Number of atoms          : 1141 (23370 expanded)
%              Number of equality atoms :  216 ( 474 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_1533,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1830,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_385,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_399,plain,
    ( ~ l1_waybel_9(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_385])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_767,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_399,c_26])).

cnf(c_768,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_1531,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_768])).

cnf(c_1845,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1830,c_1531])).

cnf(c_22,negated_conjecture,
    ( v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_410,plain,
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

cnf(c_411,plain,
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
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_32,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_730,plain,
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
    inference(resolution_lifted,[status(thm)],[c_411,c_32])).

cnf(c_731,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_60,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_93,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_735,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v3_yellow_6(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_33,c_28,c_26,c_60,c_93])).

cnf(c_736,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_782,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_736])).

cnf(c_783,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_782])).

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

cnf(c_785,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_25,c_24,c_23,c_21])).

cnf(c_1530,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_785])).

cnf(c_1832,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

cnf(c_1848,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1832,c_1531])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_772,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_773,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_773])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_947,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_28,c_26,c_60,c_93])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_947])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_773])).

cnf(c_921,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_28,c_26,c_60,c_93])).

cnf(c_10,plain,
    ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_197,c_773])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_898,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_28,c_26,c_60,c_93])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_898])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_925,c_899])).

cnf(c_959,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_948,c_937])).

cnf(c_1526,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71) ),
    inference(subtyping,[status(esa)],[c_959])).

cnf(c_1836,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_1882,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1836,c_1531])).

cnf(c_2236,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1882])).

cnf(c_2836,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1845,c_2236])).

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

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_29,c_26,c_60])).

cnf(c_1532,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71) ),
    inference(subtyping,[status(esa)],[c_665])).

cnf(c_1831,plain,
    ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1532])).

cnf(c_1875,plain,
    ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1831,c_1531])).

cnf(c_2110,plain,
    ( k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1875])).

cnf(c_2540,plain,
    ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1845,c_2110])).

cnf(c_2851,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2836,c_2540])).

cnf(c_864,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_773])).

cnf(c_865,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_864])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_865,c_28,c_26,c_60,c_93])).

cnf(c_870,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_869])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_882,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_773])).

cnf(c_883,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_84,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_885,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_883,c_28,c_26,c_60,c_84,c_93])).

cnf(c_1111,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | k2_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_885])).

cnf(c_1112,plain,
    ( ~ v1_funct_2(X0,k2_struct_0(sK1),X1)
    | ~ m1_subset_1(X2,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(k2_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1111])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X3)))
    | ~ v1_funct_1(X2)
    | k3_funct_2(k2_struct_0(sK1),X3,X2,X1) = k1_funct_1(X2,X1)
    | k4_waybel_1(sK1,X0) != X2
    | u1_struct_0(sK1) != X3
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_870,c_1112])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1241])).

cnf(c_57,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_96,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_99,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1246,plain,
    ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_28,c_26,c_57,c_60,c_93,c_96,c_99,c_921])).

cnf(c_1247,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
    inference(renaming,[status(thm)],[c_1246])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
    inference(subtyping,[status(esa)],[c_1247])).

cnf(c_1840,plain,
    ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_1907,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1840,c_1531])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_948])).

cnf(c_1835,plain,
    ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1527])).

cnf(c_1863,plain,
    ( m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1835,c_1531])).

cnf(c_1912,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1907,c_1863])).

cnf(c_3002,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1912])).

cnf(c_3422,plain,
    ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1845,c_3002])).

cnf(c_4767,plain,
    ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2851,c_3422])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1024,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_773])).

cnf(c_1025,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_28,c_26,c_60,c_93])).

cnf(c_1030,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(renaming,[status(thm)],[c_1029])).

cnf(c_1090,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2)
    | k2_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1030,c_885])).

cnf(c_1091,plain,
    ( ~ v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(k2_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X2)
    | k2_yellow_6(k2_struct_0(sK1),sK1,X2,X1) = k1_funct_1(X2,X1)
    | k4_waybel_1(sK1,X0) != X2
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_870,c_1091])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_1222,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1218,c_28,c_26,c_57,c_60,c_93,c_96,c_99,c_921])).

cnf(c_1223,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
    inference(renaming,[status(thm)],[c_1222])).

cnf(c_1523,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
    | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
    inference(subtyping,[status(esa)],[c_1223])).

cnf(c_1839,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1898,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1839,c_1531])).

cnf(c_1903,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
    | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1898,c_1863])).

cnf(c_2561,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1903])).

cnf(c_2857,plain,
    ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1845,c_2561])).

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

cnf(c_598,plain,
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

cnf(c_599,plain,
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
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_31,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_603,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26])).

cnf(c_604,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_793,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_604])).

cnf(c_794,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_796,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_25,c_24,c_23,c_21])).

cnf(c_797,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_796])).

cnf(c_1144,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_797,c_870])).

cnf(c_1375,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_1144])).

cnf(c_1521,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_1375])).

cnf(c_1536,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1521])).

cnf(c_1841,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_1916,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1841,c_1531])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1557,plain,
    ( X0_71 != X1_71
    | k4_waybel_1(X0_70,X0_71) = k4_waybel_1(X0_70,X1_71) ),
    theory(equality)).

cnf(c_1572,plain,
    ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_1541,plain,
    ( X0_71 = X0_71 ),
    theory(equality)).

cnf(c_1582,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1528,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0_71)) ),
    inference(subtyping,[status(esa)],[c_925])).

cnf(c_1594,plain,
    ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,X0_71)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_1596,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1535,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1521])).

cnf(c_1616,plain,
    ( k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_1618,plain,
    ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_1963,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2422,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_47,c_1572,c_1582,c_1596,c_1618,c_1963,c_1845])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_843,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_844,c_28,c_26,c_25,c_60,c_93])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2) ),
    inference(subtyping,[status(esa)],[c_848])).

cnf(c_1833,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
    | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1858,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
    | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1833,c_1531])).

cnf(c_2021,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1845,c_1858])).

cnf(c_2426,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2422,c_2021])).

cnf(c_2940,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2857,c_2426])).

cnf(c_5745,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4767,c_2940])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5745,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.05  
% 3.01/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.05  
% 3.01/1.05  ------  iProver source info
% 3.01/1.05  
% 3.01/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.05  git: non_committed_changes: false
% 3.01/1.05  git: last_make_outside_of_git: false
% 3.01/1.05  
% 3.01/1.05  ------ 
% 3.01/1.05  
% 3.01/1.05  ------ Input Options
% 3.01/1.05  
% 3.01/1.05  --out_options                           all
% 3.01/1.05  --tptp_safe_out                         true
% 3.01/1.05  --problem_path                          ""
% 3.01/1.05  --include_path                          ""
% 3.01/1.05  --clausifier                            res/vclausify_rel
% 3.01/1.05  --clausifier_options                    --mode clausify
% 3.01/1.05  --stdin                                 false
% 3.01/1.05  --stats_out                             all
% 3.01/1.05  
% 3.01/1.05  ------ General Options
% 3.01/1.05  
% 3.01/1.05  --fof                                   false
% 3.01/1.05  --time_out_real                         305.
% 3.01/1.05  --time_out_virtual                      -1.
% 3.01/1.05  --symbol_type_check                     false
% 3.01/1.05  --clausify_out                          false
% 3.01/1.05  --sig_cnt_out                           false
% 3.01/1.05  --trig_cnt_out                          false
% 3.01/1.05  --trig_cnt_out_tolerance                1.
% 3.01/1.05  --trig_cnt_out_sk_spl                   false
% 3.01/1.05  --abstr_cl_out                          false
% 3.01/1.05  
% 3.01/1.05  ------ Global Options
% 3.01/1.05  
% 3.01/1.05  --schedule                              default
% 3.01/1.05  --add_important_lit                     false
% 3.01/1.05  --prop_solver_per_cl                    1000
% 3.01/1.05  --min_unsat_core                        false
% 3.01/1.05  --soft_assumptions                      false
% 3.01/1.05  --soft_lemma_size                       3
% 3.01/1.05  --prop_impl_unit_size                   0
% 3.01/1.05  --prop_impl_unit                        []
% 3.01/1.05  --share_sel_clauses                     true
% 3.01/1.05  --reset_solvers                         false
% 3.01/1.05  --bc_imp_inh                            [conj_cone]
% 3.01/1.05  --conj_cone_tolerance                   3.
% 3.01/1.05  --extra_neg_conj                        none
% 3.01/1.05  --large_theory_mode                     true
% 3.01/1.05  --prolific_symb_bound                   200
% 3.01/1.05  --lt_threshold                          2000
% 3.01/1.05  --clause_weak_htbl                      true
% 3.01/1.05  --gc_record_bc_elim                     false
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing Options
% 3.01/1.05  
% 3.01/1.05  --preprocessing_flag                    true
% 3.01/1.05  --time_out_prep_mult                    0.1
% 3.01/1.05  --splitting_mode                        input
% 3.01/1.05  --splitting_grd                         true
% 3.01/1.05  --splitting_cvd                         false
% 3.01/1.05  --splitting_cvd_svl                     false
% 3.01/1.05  --splitting_nvd                         32
% 3.01/1.05  --sub_typing                            true
% 3.01/1.05  --prep_gs_sim                           true
% 3.01/1.05  --prep_unflatten                        true
% 3.01/1.05  --prep_res_sim                          true
% 3.01/1.05  --prep_upred                            true
% 3.01/1.05  --prep_sem_filter                       exhaustive
% 3.01/1.05  --prep_sem_filter_out                   false
% 3.01/1.05  --pred_elim                             true
% 3.01/1.05  --res_sim_input                         true
% 3.01/1.05  --eq_ax_congr_red                       true
% 3.01/1.05  --pure_diseq_elim                       true
% 3.01/1.05  --brand_transform                       false
% 3.01/1.05  --non_eq_to_eq                          false
% 3.01/1.05  --prep_def_merge                        true
% 3.01/1.05  --prep_def_merge_prop_impl              false
% 3.01/1.05  --prep_def_merge_mbd                    true
% 3.01/1.05  --prep_def_merge_tr_red                 false
% 3.01/1.05  --prep_def_merge_tr_cl                  false
% 3.01/1.05  --smt_preprocessing                     true
% 3.01/1.05  --smt_ac_axioms                         fast
% 3.01/1.05  --preprocessed_out                      false
% 3.01/1.05  --preprocessed_stats                    false
% 3.01/1.05  
% 3.01/1.05  ------ Abstraction refinement Options
% 3.01/1.05  
% 3.01/1.05  --abstr_ref                             []
% 3.01/1.05  --abstr_ref_prep                        false
% 3.01/1.05  --abstr_ref_until_sat                   false
% 3.01/1.05  --abstr_ref_sig_restrict                funpre
% 3.01/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.05  --abstr_ref_under                       []
% 3.01/1.05  
% 3.01/1.05  ------ SAT Options
% 3.01/1.05  
% 3.01/1.05  --sat_mode                              false
% 3.01/1.05  --sat_fm_restart_options                ""
% 3.01/1.05  --sat_gr_def                            false
% 3.01/1.05  --sat_epr_types                         true
% 3.01/1.05  --sat_non_cyclic_types                  false
% 3.01/1.05  --sat_finite_models                     false
% 3.01/1.05  --sat_fm_lemmas                         false
% 3.01/1.05  --sat_fm_prep                           false
% 3.01/1.05  --sat_fm_uc_incr                        true
% 3.01/1.05  --sat_out_model                         small
% 3.01/1.05  --sat_out_clauses                       false
% 3.01/1.05  
% 3.01/1.05  ------ QBF Options
% 3.01/1.05  
% 3.01/1.05  --qbf_mode                              false
% 3.01/1.05  --qbf_elim_univ                         false
% 3.01/1.05  --qbf_dom_inst                          none
% 3.01/1.05  --qbf_dom_pre_inst                      false
% 3.01/1.05  --qbf_sk_in                             false
% 3.01/1.05  --qbf_pred_elim                         true
% 3.01/1.05  --qbf_split                             512
% 3.01/1.05  
% 3.01/1.05  ------ BMC1 Options
% 3.01/1.05  
% 3.01/1.05  --bmc1_incremental                      false
% 3.01/1.05  --bmc1_axioms                           reachable_all
% 3.01/1.05  --bmc1_min_bound                        0
% 3.01/1.05  --bmc1_max_bound                        -1
% 3.01/1.05  --bmc1_max_bound_default                -1
% 3.01/1.05  --bmc1_symbol_reachability              true
% 3.01/1.05  --bmc1_property_lemmas                  false
% 3.01/1.05  --bmc1_k_induction                      false
% 3.01/1.05  --bmc1_non_equiv_states                 false
% 3.01/1.05  --bmc1_deadlock                         false
% 3.01/1.05  --bmc1_ucm                              false
% 3.01/1.05  --bmc1_add_unsat_core                   none
% 3.01/1.05  --bmc1_unsat_core_children              false
% 3.01/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.05  --bmc1_out_stat                         full
% 3.01/1.05  --bmc1_ground_init                      false
% 3.01/1.05  --bmc1_pre_inst_next_state              false
% 3.01/1.05  --bmc1_pre_inst_state                   false
% 3.01/1.05  --bmc1_pre_inst_reach_state             false
% 3.01/1.05  --bmc1_out_unsat_core                   false
% 3.01/1.05  --bmc1_aig_witness_out                  false
% 3.01/1.05  --bmc1_verbose                          false
% 3.01/1.05  --bmc1_dump_clauses_tptp                false
% 3.01/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.05  --bmc1_dump_file                        -
% 3.01/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.05  --bmc1_ucm_extend_mode                  1
% 3.01/1.05  --bmc1_ucm_init_mode                    2
% 3.01/1.05  --bmc1_ucm_cone_mode                    none
% 3.01/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.05  --bmc1_ucm_relax_model                  4
% 3.01/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.05  --bmc1_ucm_layered_model                none
% 3.01/1.05  --bmc1_ucm_max_lemma_size               10
% 3.01/1.05  
% 3.01/1.05  ------ AIG Options
% 3.01/1.05  
% 3.01/1.05  --aig_mode                              false
% 3.01/1.05  
% 3.01/1.05  ------ Instantiation Options
% 3.01/1.05  
% 3.01/1.05  --instantiation_flag                    true
% 3.01/1.05  --inst_sos_flag                         false
% 3.01/1.05  --inst_sos_phase                        true
% 3.01/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.05  --inst_lit_sel_side                     num_symb
% 3.01/1.05  --inst_solver_per_active                1400
% 3.01/1.05  --inst_solver_calls_frac                1.
% 3.01/1.05  --inst_passive_queue_type               priority_queues
% 3.01/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.05  --inst_passive_queues_freq              [25;2]
% 3.01/1.05  --inst_dismatching                      true
% 3.01/1.05  --inst_eager_unprocessed_to_passive     true
% 3.01/1.05  --inst_prop_sim_given                   true
% 3.01/1.05  --inst_prop_sim_new                     false
% 3.01/1.05  --inst_subs_new                         false
% 3.01/1.05  --inst_eq_res_simp                      false
% 3.01/1.05  --inst_subs_given                       false
% 3.01/1.05  --inst_orphan_elimination               true
% 3.01/1.05  --inst_learning_loop_flag               true
% 3.01/1.05  --inst_learning_start                   3000
% 3.01/1.05  --inst_learning_factor                  2
% 3.01/1.05  --inst_start_prop_sim_after_learn       3
% 3.01/1.05  --inst_sel_renew                        solver
% 3.01/1.05  --inst_lit_activity_flag                true
% 3.01/1.05  --inst_restr_to_given                   false
% 3.01/1.05  --inst_activity_threshold               500
% 3.01/1.05  --inst_out_proof                        true
% 3.01/1.05  
% 3.01/1.05  ------ Resolution Options
% 3.01/1.05  
% 3.01/1.05  --resolution_flag                       true
% 3.01/1.05  --res_lit_sel                           adaptive
% 3.01/1.05  --res_lit_sel_side                      none
% 3.01/1.05  --res_ordering                          kbo
% 3.01/1.05  --res_to_prop_solver                    active
% 3.01/1.05  --res_prop_simpl_new                    false
% 3.01/1.05  --res_prop_simpl_given                  true
% 3.01/1.05  --res_passive_queue_type                priority_queues
% 3.01/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.05  --res_passive_queues_freq               [15;5]
% 3.01/1.05  --res_forward_subs                      full
% 3.01/1.05  --res_backward_subs                     full
% 3.01/1.05  --res_forward_subs_resolution           true
% 3.01/1.05  --res_backward_subs_resolution          true
% 3.01/1.05  --res_orphan_elimination                true
% 3.01/1.05  --res_time_limit                        2.
% 3.01/1.05  --res_out_proof                         true
% 3.01/1.05  
% 3.01/1.05  ------ Superposition Options
% 3.01/1.05  
% 3.01/1.05  --superposition_flag                    true
% 3.01/1.05  --sup_passive_queue_type                priority_queues
% 3.01/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.05  --demod_completeness_check              fast
% 3.01/1.05  --demod_use_ground                      true
% 3.01/1.05  --sup_to_prop_solver                    passive
% 3.01/1.05  --sup_prop_simpl_new                    true
% 3.01/1.05  --sup_prop_simpl_given                  true
% 3.01/1.05  --sup_fun_splitting                     false
% 3.01/1.05  --sup_smt_interval                      50000
% 3.01/1.05  
% 3.01/1.05  ------ Superposition Simplification Setup
% 3.01/1.05  
% 3.01/1.05  --sup_indices_passive                   []
% 3.01/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_full_bw                           [BwDemod]
% 3.01/1.05  --sup_immed_triv                        [TrivRules]
% 3.01/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_immed_bw_main                     []
% 3.01/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.05  
% 3.01/1.05  ------ Combination Options
% 3.01/1.05  
% 3.01/1.05  --comb_res_mult                         3
% 3.01/1.05  --comb_sup_mult                         2
% 3.01/1.05  --comb_inst_mult                        10
% 3.01/1.05  
% 3.01/1.05  ------ Debug Options
% 3.01/1.05  
% 3.01/1.05  --dbg_backtrace                         false
% 3.01/1.05  --dbg_dump_prop_clauses                 false
% 3.01/1.05  --dbg_dump_prop_clauses_file            -
% 3.01/1.05  --dbg_out_stat                          false
% 3.01/1.05  ------ Parsing...
% 3.01/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.05  ------ Proving...
% 3.01/1.05  ------ Problem Properties 
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  clauses                                 15
% 3.01/1.05  conjectures                             2
% 3.01/1.05  EPR                                     0
% 3.01/1.05  Horn                                    13
% 3.01/1.05  unary                                   4
% 3.01/1.05  binary                                  3
% 3.01/1.05  lits                                    39
% 3.01/1.05  lits eq                                 10
% 3.01/1.05  fd_pure                                 0
% 3.01/1.05  fd_pseudo                               0
% 3.01/1.05  fd_cond                                 0
% 3.01/1.05  fd_pseudo_cond                          0
% 3.01/1.05  AC symbols                              0
% 3.01/1.05  
% 3.01/1.05  ------ Schedule dynamic 5 is on 
% 3.01/1.05  
% 3.01/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  ------ 
% 3.01/1.05  Current options:
% 3.01/1.05  ------ 
% 3.01/1.05  
% 3.01/1.05  ------ Input Options
% 3.01/1.05  
% 3.01/1.05  --out_options                           all
% 3.01/1.05  --tptp_safe_out                         true
% 3.01/1.05  --problem_path                          ""
% 3.01/1.05  --include_path                          ""
% 3.01/1.05  --clausifier                            res/vclausify_rel
% 3.01/1.05  --clausifier_options                    --mode clausify
% 3.01/1.05  --stdin                                 false
% 3.01/1.05  --stats_out                             all
% 3.01/1.05  
% 3.01/1.05  ------ General Options
% 3.01/1.05  
% 3.01/1.05  --fof                                   false
% 3.01/1.05  --time_out_real                         305.
% 3.01/1.05  --time_out_virtual                      -1.
% 3.01/1.05  --symbol_type_check                     false
% 3.01/1.05  --clausify_out                          false
% 3.01/1.05  --sig_cnt_out                           false
% 3.01/1.05  --trig_cnt_out                          false
% 3.01/1.05  --trig_cnt_out_tolerance                1.
% 3.01/1.05  --trig_cnt_out_sk_spl                   false
% 3.01/1.05  --abstr_cl_out                          false
% 3.01/1.05  
% 3.01/1.05  ------ Global Options
% 3.01/1.05  
% 3.01/1.05  --schedule                              default
% 3.01/1.05  --add_important_lit                     false
% 3.01/1.05  --prop_solver_per_cl                    1000
% 3.01/1.05  --min_unsat_core                        false
% 3.01/1.05  --soft_assumptions                      false
% 3.01/1.05  --soft_lemma_size                       3
% 3.01/1.05  --prop_impl_unit_size                   0
% 3.01/1.05  --prop_impl_unit                        []
% 3.01/1.05  --share_sel_clauses                     true
% 3.01/1.05  --reset_solvers                         false
% 3.01/1.05  --bc_imp_inh                            [conj_cone]
% 3.01/1.05  --conj_cone_tolerance                   3.
% 3.01/1.05  --extra_neg_conj                        none
% 3.01/1.05  --large_theory_mode                     true
% 3.01/1.05  --prolific_symb_bound                   200
% 3.01/1.05  --lt_threshold                          2000
% 3.01/1.05  --clause_weak_htbl                      true
% 3.01/1.05  --gc_record_bc_elim                     false
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing Options
% 3.01/1.05  
% 3.01/1.05  --preprocessing_flag                    true
% 3.01/1.05  --time_out_prep_mult                    0.1
% 3.01/1.05  --splitting_mode                        input
% 3.01/1.05  --splitting_grd                         true
% 3.01/1.05  --splitting_cvd                         false
% 3.01/1.05  --splitting_cvd_svl                     false
% 3.01/1.05  --splitting_nvd                         32
% 3.01/1.05  --sub_typing                            true
% 3.01/1.05  --prep_gs_sim                           true
% 3.01/1.05  --prep_unflatten                        true
% 3.01/1.05  --prep_res_sim                          true
% 3.01/1.05  --prep_upred                            true
% 3.01/1.05  --prep_sem_filter                       exhaustive
% 3.01/1.05  --prep_sem_filter_out                   false
% 3.01/1.05  --pred_elim                             true
% 3.01/1.05  --res_sim_input                         true
% 3.01/1.05  --eq_ax_congr_red                       true
% 3.01/1.05  --pure_diseq_elim                       true
% 3.01/1.05  --brand_transform                       false
% 3.01/1.05  --non_eq_to_eq                          false
% 3.01/1.05  --prep_def_merge                        true
% 3.01/1.05  --prep_def_merge_prop_impl              false
% 3.01/1.05  --prep_def_merge_mbd                    true
% 3.01/1.05  --prep_def_merge_tr_red                 false
% 3.01/1.05  --prep_def_merge_tr_cl                  false
% 3.01/1.05  --smt_preprocessing                     true
% 3.01/1.05  --smt_ac_axioms                         fast
% 3.01/1.05  --preprocessed_out                      false
% 3.01/1.05  --preprocessed_stats                    false
% 3.01/1.05  
% 3.01/1.05  ------ Abstraction refinement Options
% 3.01/1.05  
% 3.01/1.05  --abstr_ref                             []
% 3.01/1.05  --abstr_ref_prep                        false
% 3.01/1.05  --abstr_ref_until_sat                   false
% 3.01/1.05  --abstr_ref_sig_restrict                funpre
% 3.01/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.05  --abstr_ref_under                       []
% 3.01/1.05  
% 3.01/1.05  ------ SAT Options
% 3.01/1.05  
% 3.01/1.05  --sat_mode                              false
% 3.01/1.05  --sat_fm_restart_options                ""
% 3.01/1.05  --sat_gr_def                            false
% 3.01/1.05  --sat_epr_types                         true
% 3.01/1.05  --sat_non_cyclic_types                  false
% 3.01/1.05  --sat_finite_models                     false
% 3.01/1.05  --sat_fm_lemmas                         false
% 3.01/1.05  --sat_fm_prep                           false
% 3.01/1.05  --sat_fm_uc_incr                        true
% 3.01/1.05  --sat_out_model                         small
% 3.01/1.05  --sat_out_clauses                       false
% 3.01/1.05  
% 3.01/1.05  ------ QBF Options
% 3.01/1.05  
% 3.01/1.05  --qbf_mode                              false
% 3.01/1.05  --qbf_elim_univ                         false
% 3.01/1.05  --qbf_dom_inst                          none
% 3.01/1.05  --qbf_dom_pre_inst                      false
% 3.01/1.05  --qbf_sk_in                             false
% 3.01/1.05  --qbf_pred_elim                         true
% 3.01/1.05  --qbf_split                             512
% 3.01/1.05  
% 3.01/1.05  ------ BMC1 Options
% 3.01/1.05  
% 3.01/1.05  --bmc1_incremental                      false
% 3.01/1.05  --bmc1_axioms                           reachable_all
% 3.01/1.05  --bmc1_min_bound                        0
% 3.01/1.05  --bmc1_max_bound                        -1
% 3.01/1.05  --bmc1_max_bound_default                -1
% 3.01/1.05  --bmc1_symbol_reachability              true
% 3.01/1.05  --bmc1_property_lemmas                  false
% 3.01/1.05  --bmc1_k_induction                      false
% 3.01/1.05  --bmc1_non_equiv_states                 false
% 3.01/1.05  --bmc1_deadlock                         false
% 3.01/1.05  --bmc1_ucm                              false
% 3.01/1.05  --bmc1_add_unsat_core                   none
% 3.01/1.05  --bmc1_unsat_core_children              false
% 3.01/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.05  --bmc1_out_stat                         full
% 3.01/1.05  --bmc1_ground_init                      false
% 3.01/1.05  --bmc1_pre_inst_next_state              false
% 3.01/1.05  --bmc1_pre_inst_state                   false
% 3.01/1.05  --bmc1_pre_inst_reach_state             false
% 3.01/1.05  --bmc1_out_unsat_core                   false
% 3.01/1.05  --bmc1_aig_witness_out                  false
% 3.01/1.05  --bmc1_verbose                          false
% 3.01/1.05  --bmc1_dump_clauses_tptp                false
% 3.01/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.05  --bmc1_dump_file                        -
% 3.01/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.05  --bmc1_ucm_extend_mode                  1
% 3.01/1.05  --bmc1_ucm_init_mode                    2
% 3.01/1.05  --bmc1_ucm_cone_mode                    none
% 3.01/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.05  --bmc1_ucm_relax_model                  4
% 3.01/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.05  --bmc1_ucm_layered_model                none
% 3.01/1.05  --bmc1_ucm_max_lemma_size               10
% 3.01/1.05  
% 3.01/1.05  ------ AIG Options
% 3.01/1.05  
% 3.01/1.05  --aig_mode                              false
% 3.01/1.05  
% 3.01/1.05  ------ Instantiation Options
% 3.01/1.05  
% 3.01/1.05  --instantiation_flag                    true
% 3.01/1.05  --inst_sos_flag                         false
% 3.01/1.05  --inst_sos_phase                        true
% 3.01/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.05  --inst_lit_sel_side                     none
% 3.01/1.05  --inst_solver_per_active                1400
% 3.01/1.05  --inst_solver_calls_frac                1.
% 3.01/1.05  --inst_passive_queue_type               priority_queues
% 3.01/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.05  --inst_passive_queues_freq              [25;2]
% 3.01/1.05  --inst_dismatching                      true
% 3.01/1.05  --inst_eager_unprocessed_to_passive     true
% 3.01/1.05  --inst_prop_sim_given                   true
% 3.01/1.05  --inst_prop_sim_new                     false
% 3.01/1.05  --inst_subs_new                         false
% 3.01/1.05  --inst_eq_res_simp                      false
% 3.01/1.05  --inst_subs_given                       false
% 3.01/1.05  --inst_orphan_elimination               true
% 3.01/1.05  --inst_learning_loop_flag               true
% 3.01/1.05  --inst_learning_start                   3000
% 3.01/1.05  --inst_learning_factor                  2
% 3.01/1.05  --inst_start_prop_sim_after_learn       3
% 3.01/1.05  --inst_sel_renew                        solver
% 3.01/1.05  --inst_lit_activity_flag                true
% 3.01/1.05  --inst_restr_to_given                   false
% 3.01/1.05  --inst_activity_threshold               500
% 3.01/1.05  --inst_out_proof                        true
% 3.01/1.05  
% 3.01/1.05  ------ Resolution Options
% 3.01/1.05  
% 3.01/1.05  --resolution_flag                       false
% 3.01/1.05  --res_lit_sel                           adaptive
% 3.01/1.05  --res_lit_sel_side                      none
% 3.01/1.05  --res_ordering                          kbo
% 3.01/1.05  --res_to_prop_solver                    active
% 3.01/1.05  --res_prop_simpl_new                    false
% 3.01/1.05  --res_prop_simpl_given                  true
% 3.01/1.05  --res_passive_queue_type                priority_queues
% 3.01/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.05  --res_passive_queues_freq               [15;5]
% 3.01/1.05  --res_forward_subs                      full
% 3.01/1.05  --res_backward_subs                     full
% 3.01/1.05  --res_forward_subs_resolution           true
% 3.01/1.05  --res_backward_subs_resolution          true
% 3.01/1.05  --res_orphan_elimination                true
% 3.01/1.05  --res_time_limit                        2.
% 3.01/1.05  --res_out_proof                         true
% 3.01/1.05  
% 3.01/1.05  ------ Superposition Options
% 3.01/1.05  
% 3.01/1.05  --superposition_flag                    true
% 3.01/1.05  --sup_passive_queue_type                priority_queues
% 3.01/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.05  --demod_completeness_check              fast
% 3.01/1.05  --demod_use_ground                      true
% 3.01/1.05  --sup_to_prop_solver                    passive
% 3.01/1.05  --sup_prop_simpl_new                    true
% 3.01/1.05  --sup_prop_simpl_given                  true
% 3.01/1.05  --sup_fun_splitting                     false
% 3.01/1.05  --sup_smt_interval                      50000
% 3.01/1.05  
% 3.01/1.05  ------ Superposition Simplification Setup
% 3.01/1.05  
% 3.01/1.05  --sup_indices_passive                   []
% 3.01/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_full_bw                           [BwDemod]
% 3.01/1.05  --sup_immed_triv                        [TrivRules]
% 3.01/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_immed_bw_main                     []
% 3.01/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.05  
% 3.01/1.05  ------ Combination Options
% 3.01/1.05  
% 3.01/1.05  --comb_res_mult                         3
% 3.01/1.05  --comb_sup_mult                         2
% 3.01/1.05  --comb_inst_mult                        10
% 3.01/1.05  
% 3.01/1.05  ------ Debug Options
% 3.01/1.05  
% 3.01/1.05  --dbg_backtrace                         false
% 3.01/1.05  --dbg_dump_prop_clauses                 false
% 3.01/1.05  --dbg_dump_prop_clauses_file            -
% 3.01/1.05  --dbg_out_stat                          false
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  ------ Proving...
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  % SZS status Theorem for theBenchmark.p
% 3.01/1.05  
% 3.01/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.05  
% 3.01/1.05  fof(f14,conjecture,(
% 3.01/1.05    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f15,negated_conjecture,(
% 3.01/1.05    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 3.01/1.05    inference(negated_conjecture,[],[f14])).
% 3.01/1.05  
% 3.01/1.05  fof(f39,plain,(
% 3.01/1.05    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f15])).
% 3.01/1.05  
% 3.01/1.05  fof(f40,plain,(
% 3.01/1.05    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 3.01/1.05    inference(flattening,[],[f39])).
% 3.01/1.05  
% 3.01/1.05  fof(f47,plain,(
% 3.01/1.05    ( ! [X0,X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1))) & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.01/1.05    introduced(choice_axiom,[])).
% 3.01/1.05  
% 3.01/1.05  fof(f46,plain,(
% 3.01/1.05    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,sK2)),k10_yellow_6(X0,k3_waybel_2(X0,X2,sK2))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2,X0) & v3_yellow_6(sK2,X0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 3.01/1.05    introduced(choice_axiom,[])).
% 3.01/1.05  
% 3.01/1.05  fof(f45,plain,(
% 3.01/1.05    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK1,X2,k11_yellow_6(sK1,X1)),k10_yellow_6(sK1,k3_waybel_2(sK1,X2,X1))) & v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(X1,sK1) & v3_yellow_6(X1,sK1) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.01/1.05    introduced(choice_axiom,[])).
% 3.01/1.05  
% 3.01/1.05  fof(f48,plain,(
% 3.01/1.05    ((~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) & v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) & m1_subset_1(sK3,u1_struct_0(sK1))) & l1_waybel_0(sK2,sK1) & v3_yellow_6(sK2,sK1) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.01/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f47,f46,f45])).
% 3.01/1.05  
% 3.01/1.05  fof(f80,plain,(
% 3.01/1.05    m1_subset_1(sK3,u1_struct_0(sK1))),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f11,axiom,(
% 3.01/1.05    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f34,plain,(
% 3.01/1.05    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 3.01/1.05    inference(ennf_transformation,[],[f11])).
% 3.01/1.05  
% 3.01/1.05  fof(f63,plain,(
% 3.01/1.05    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f34])).
% 3.01/1.05  
% 3.01/1.05  fof(f3,axiom,(
% 3.01/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f19,plain,(
% 3.01/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.01/1.05    inference(ennf_transformation,[],[f3])).
% 3.01/1.05  
% 3.01/1.05  fof(f51,plain,(
% 3.01/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f19])).
% 3.01/1.05  
% 3.01/1.05  fof(f2,axiom,(
% 3.01/1.05    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f18,plain,(
% 3.01/1.05    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.01/1.05    inference(ennf_transformation,[],[f2])).
% 3.01/1.05  
% 3.01/1.05  fof(f50,plain,(
% 3.01/1.05    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f18])).
% 3.01/1.05  
% 3.01/1.05  fof(f74,plain,(
% 3.01/1.05    l1_waybel_9(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f78,plain,(
% 3.01/1.05    v3_yellow_6(sK2,sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f6,axiom,(
% 3.01/1.05    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f24,plain,(
% 3.01/1.05    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f6])).
% 3.01/1.05  
% 3.01/1.05  fof(f25,plain,(
% 3.01/1.05    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(flattening,[],[f24])).
% 3.01/1.05  
% 3.01/1.05  fof(f54,plain,(
% 3.01/1.05    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f25])).
% 3.01/1.05  
% 3.01/1.05  fof(f68,plain,(
% 3.01/1.05    v8_pre_topc(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f67,plain,(
% 3.01/1.05    v2_pre_topc(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f72,plain,(
% 3.01/1.05    v1_lattice3(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f64,plain,(
% 3.01/1.05    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f34])).
% 3.01/1.05  
% 3.01/1.05  fof(f4,axiom,(
% 3.01/1.05    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f20,plain,(
% 3.01/1.05    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.01/1.05    inference(ennf_transformation,[],[f4])).
% 3.01/1.05  
% 3.01/1.05  fof(f21,plain,(
% 3.01/1.05    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.01/1.05    inference(flattening,[],[f20])).
% 3.01/1.05  
% 3.01/1.05  fof(f52,plain,(
% 3.01/1.05    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f21])).
% 3.01/1.05  
% 3.01/1.05  fof(f75,plain,(
% 3.01/1.05    ~v2_struct_0(sK2)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f76,plain,(
% 3.01/1.05    v4_orders_2(sK2)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f77,plain,(
% 3.01/1.05    v7_waybel_0(sK2)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f79,plain,(
% 3.01/1.05    l1_waybel_0(sK2,sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f10,axiom,(
% 3.01/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f32,plain,(
% 3.01/1.05    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f10])).
% 3.01/1.05  
% 3.01/1.05  fof(f33,plain,(
% 3.01/1.05    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(flattening,[],[f32])).
% 3.01/1.05  
% 3.01/1.05  fof(f62,plain,(
% 3.01/1.05    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f33])).
% 3.01/1.05  
% 3.01/1.05  fof(f60,plain,(
% 3.01/1.05    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f33])).
% 3.01/1.05  
% 3.01/1.05  fof(f9,axiom,(
% 3.01/1.05    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f30,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f9])).
% 3.01/1.05  
% 3.01/1.05  fof(f31,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(flattening,[],[f30])).
% 3.01/1.05  
% 3.01/1.05  fof(f41,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(nnf_transformation,[],[f31])).
% 3.01/1.05  
% 3.01/1.05  fof(f42,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(rectify,[],[f41])).
% 3.01/1.05  
% 3.01/1.05  fof(f43,plain,(
% 3.01/1.05    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.01/1.05    introduced(choice_axiom,[])).
% 3.01/1.05  
% 3.01/1.05  fof(f44,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.01/1.05  
% 3.01/1.05  fof(f57,plain,(
% 3.01/1.05    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f44])).
% 3.01/1.05  
% 3.01/1.05  fof(f83,plain,(
% 3.01/1.05    ( ! [X4,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(equality_resolution,[],[f57])).
% 3.01/1.05  
% 3.01/1.05  fof(f61,plain,(
% 3.01/1.05    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f33])).
% 3.01/1.05  
% 3.01/1.05  fof(f5,axiom,(
% 3.01/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f22,plain,(
% 3.01/1.05    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f5])).
% 3.01/1.05  
% 3.01/1.05  fof(f23,plain,(
% 3.01/1.05    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.01/1.05    inference(flattening,[],[f22])).
% 3.01/1.05  
% 3.01/1.05  fof(f53,plain,(
% 3.01/1.05    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f23])).
% 3.01/1.05  
% 3.01/1.05  fof(f73,plain,(
% 3.01/1.05    v2_lattice3(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f71,plain,(
% 3.01/1.05    v5_orders_2(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f1,axiom,(
% 3.01/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f16,plain,(
% 3.01/1.05    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f1])).
% 3.01/1.05  
% 3.01/1.05  fof(f17,plain,(
% 3.01/1.05    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.01/1.05    inference(flattening,[],[f16])).
% 3.01/1.05  
% 3.01/1.05  fof(f49,plain,(
% 3.01/1.05    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f17])).
% 3.01/1.05  
% 3.01/1.05  fof(f7,axiom,(
% 3.01/1.05    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f26,plain,(
% 3.01/1.05    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f7])).
% 3.01/1.05  
% 3.01/1.05  fof(f27,plain,(
% 3.01/1.05    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(flattening,[],[f26])).
% 3.01/1.05  
% 3.01/1.05  fof(f55,plain,(
% 3.01/1.05    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f27])).
% 3.01/1.05  
% 3.01/1.05  fof(f8,axiom,(
% 3.01/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f28,plain,(
% 3.01/1.05    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f8])).
% 3.01/1.05  
% 3.01/1.05  fof(f29,plain,(
% 3.01/1.05    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 3.01/1.05    inference(flattening,[],[f28])).
% 3.01/1.05  
% 3.01/1.05  fof(f56,plain,(
% 3.01/1.05    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f29])).
% 3.01/1.05  
% 3.01/1.05  fof(f13,axiom,(
% 3.01/1.05    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f37,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f13])).
% 3.01/1.05  
% 3.01/1.05  fof(f38,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.01/1.05    inference(flattening,[],[f37])).
% 3.01/1.05  
% 3.01/1.05  fof(f66,plain,(
% 3.01/1.05    ( ! [X2,X0,X1] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f38])).
% 3.01/1.05  
% 3.01/1.05  fof(f81,plain,(
% 3.01/1.05    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f69,plain,(
% 3.01/1.05    v3_orders_2(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f70,plain,(
% 3.01/1.05    v4_orders_2(sK1)),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  fof(f12,axiom,(
% 3.01/1.05    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 3.01/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.05  
% 3.01/1.05  fof(f35,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.01/1.05    inference(ennf_transformation,[],[f12])).
% 3.01/1.05  
% 3.01/1.05  fof(f36,plain,(
% 3.01/1.05    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.01/1.05    inference(flattening,[],[f35])).
% 3.01/1.05  
% 3.01/1.05  fof(f65,plain,(
% 3.01/1.05    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.01/1.05    inference(cnf_transformation,[],[f36])).
% 3.01/1.05  
% 3.01/1.05  fof(f82,plain,(
% 3.01/1.05    ~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2)))),
% 3.01/1.05    inference(cnf_transformation,[],[f48])).
% 3.01/1.05  
% 3.01/1.05  cnf(c_20,negated_conjecture,
% 3.01/1.05      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.01/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1533,negated_conjecture,
% 3.01/1.05      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_20]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1830,plain,
% 3.01/1.05      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_15,plain,
% 3.01/1.05      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2,plain,
% 3.01/1.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f51]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1,plain,
% 3.01/1.05      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_385,plain,
% 3.01/1.05      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.05      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_399,plain,
% 3.01/1.05      ( ~ l1_waybel_9(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.05      inference(resolution,[status(thm)],[c_15,c_385]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_26,negated_conjecture,
% 3.01/1.05      ( l1_waybel_9(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_767,plain,
% 3.01/1.05      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_399,c_26]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_768,plain,
% 3.01/1.05      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_767]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1531,plain,
% 3.01/1.05      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_768]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1845,plain,
% 3.01/1.05      ( m1_subset_1(sK3,k2_struct_0(sK1)) = iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1830,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_22,negated_conjecture,
% 3.01/1.05      ( v3_yellow_6(sK2,sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_5,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,X1)
% 3.01/1.05      | ~ l1_waybel_0(X0,X1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v8_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ l1_pre_topc(X1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_410,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,X1)
% 3.01/1.05      | ~ l1_waybel_0(X0,X1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 3.01/1.05      | ~ l1_waybel_9(X2)
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v8_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | X1 != X2 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_5]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_411,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,X1)
% 3.01/1.05      | ~ l1_waybel_0(X0,X1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 3.01/1.05      | ~ l1_waybel_9(X1)
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v8_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | v2_struct_0(X1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_410]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_32,negated_conjecture,
% 3.01/1.05      ( v8_pre_topc(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_730,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,X1)
% 3.01/1.05      | ~ l1_waybel_0(X0,X1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 3.01/1.05      | ~ l1_waybel_9(X1)
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_411,c_32]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_731,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,sK1)
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 3.01/1.05      | ~ l1_waybel_9(sK1)
% 3.01/1.05      | ~ v2_pre_topc(sK1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | v2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_730]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_33,negated_conjecture,
% 3.01/1.05      ( v2_pre_topc(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_28,negated_conjecture,
% 3.01/1.05      ( v1_lattice3(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_14,plain,
% 3.01/1.05      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_60,plain,
% 3.01/1.05      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_3,plain,
% 3.01/1.05      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f52]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_93,plain,
% 3.01/1.05      ( ~ l1_orders_2(sK1) | ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_735,plain,
% 3.01/1.05      ( v2_struct_0(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | ~ v3_yellow_6(X0,sK1) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_731,c_33,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_736,plain,
% 3.01/1.05      ( ~ v3_yellow_6(X0,sK1)
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_735]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_782,plain,
% 3.01/1.05      ( ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | sK2 != X0
% 3.01/1.05      | sK1 != sK1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_22,c_736]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_783,plain,
% 3.01/1.05      ( ~ l1_waybel_0(sK2,sK1)
% 3.01/1.05      | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
% 3.01/1.05      | ~ v4_orders_2(sK2)
% 3.01/1.05      | ~ v7_waybel_0(sK2)
% 3.01/1.05      | v2_struct_0(sK2) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_782]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_25,negated_conjecture,
% 3.01/1.05      ( ~ v2_struct_0(sK2) ),
% 3.01/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_24,negated_conjecture,
% 3.01/1.05      ( v4_orders_2(sK2) ),
% 3.01/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_23,negated_conjecture,
% 3.01/1.05      ( v7_waybel_0(sK2) ),
% 3.01/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_21,negated_conjecture,
% 3.01/1.05      ( l1_waybel_0(sK2,sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_785,plain,
% 3.01/1.05      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_783,c_25,c_24,c_23,c_21]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1530,plain,
% 3.01/1.05      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_785]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1832,plain,
% 3.01/1.05      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1848,plain,
% 3.01/1.05      ( m1_subset_1(k11_yellow_6(sK1,sK2),k2_struct_0(sK1)) = iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1832,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_11,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | v2_struct_0(X1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_772,plain,
% 3.01/1.05      ( l1_orders_2(X0) | sK1 != X0 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_773,plain,
% 3.01/1.05      ( l1_orders_2(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_772]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_942,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_943,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | v2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_942]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_947,plain,
% 3.01/1.05      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_943,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_948,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_947]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_13,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 3.01/1.05      inference(cnf_transformation,[],[f60]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_920,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | v1_funct_1(k4_waybel_1(X1,X0))
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_921,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | v2_struct_0(sK1)
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_920]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_925,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_921,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_10,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.01/1.05      | ~ l1_orders_2(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 3.01/1.05      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 3.01/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_12,plain,
% 3.01/1.05      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.05      | ~ l1_orders_2(X0)
% 3.01/1.05      | v2_struct_0(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_196,plain,
% 3.01/1.05      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.01/1.05      | ~ l1_orders_2(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 3.01/1.05      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_10,c_12]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_197,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 3.01/1.05      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_196]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_893,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 3.01/1.05      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_197,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_894,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | v2_struct_0(sK1)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_893]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_898,plain,
% 3.01/1.05      ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_894,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_899,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_898]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_937,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(backward_subsumption_resolution,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_925,c_899]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_959,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(backward_subsumption_resolution,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_948,c_937]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1526,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
% 3.01/1.05      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_959]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1836,plain,
% 3.01/1.05      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1526]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1882,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k11_lattice3(sK1,X0_71,X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1836,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2236,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1848,c_1882]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2836,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1845,c_2236]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_4,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.01/1.05      | ~ v5_orders_2(X1)
% 3.01/1.05      | ~ v2_lattice3(X1)
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_27,negated_conjecture,
% 3.01/1.05      ( v2_lattice3(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_660,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.01/1.05      | ~ v5_orders_2(X1)
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_661,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ v5_orders_2(sK1)
% 3.01/1.05      | ~ l1_orders_2(sK1)
% 3.01/1.05      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_660]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_29,negated_conjecture,
% 3.01/1.05      ( v5_orders_2(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_665,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.01/1.05      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_661,c_29,c_26,c_60]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1532,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1_71,u1_struct_0(sK1))
% 3.01/1.05      | k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_665]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1831,plain,
% 3.01/1.05      ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X1_71,u1_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1532]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1875,plain,
% 3.01/1.05      ( k11_lattice3(sK1,X0_71,X1_71) = k12_lattice3(sK1,X0_71,X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1831,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2110,plain,
% 3.01/1.05      ( k11_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,X0_71,k11_yellow_6(sK1,sK2))
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1848,c_1875]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2540,plain,
% 3.01/1.05      ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1845,c_2110]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2851,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_2836,c_2540]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_864,plain,
% 3.01/1.05      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 3.01/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | sK1 != X0 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_865,plain,
% 3.01/1.05      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | v2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_864]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_869,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_865,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_870,plain,
% 3.01/1.05      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_869]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_0,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.05      | ~ m1_subset_1(X3,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.01/1.05      inference(cnf_transformation,[],[f49]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_6,plain,
% 3.01/1.05      ( ~ l1_orders_2(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.01/1.05      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_882,plain,
% 3.01/1.05      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_6,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_883,plain,
% 3.01/1.05      ( v2_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_882]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_84,plain,
% 3.01/1.05      ( ~ l1_orders_2(sK1)
% 3.01/1.05      | v2_struct_0(sK1)
% 3.01/1.05      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_885,plain,
% 3.01/1.05      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_883,c_28,c_26,c_60,c_84,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1111,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.05      | ~ m1_subset_1(X3,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.01/1.05      | k2_struct_0(sK1) != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_885]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1112,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,k2_struct_0(sK1),X1)
% 3.01/1.05      | ~ m1_subset_1(X2,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X1)))
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k3_funct_2(k2_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_1111]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1241,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X3)))
% 3.01/1.05      | ~ v1_funct_1(X2)
% 3.01/1.05      | k3_funct_2(k2_struct_0(sK1),X3,X2,X1) = k1_funct_1(X2,X1)
% 3.01/1.05      | k4_waybel_1(sK1,X0) != X2
% 3.01/1.05      | u1_struct_0(sK1) != X3
% 3.01/1.05      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_870,c_1112]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1242,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 3.01/1.05      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 3.01/1.05      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_1241]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_57,plain,
% 3.01/1.05      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_15]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_96,plain,
% 3.01/1.05      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_99,plain,
% 3.01/1.05      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1246,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1242,c_28,c_26,c_57,c_60,c_93,c_96,c_99,c_921]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1247,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_1246]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1522,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_1247]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1840,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1907,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1840,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1527,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_948]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1835,plain,
% 3.01/1.05      ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1527]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1863,plain,
% 3.01/1.05      ( m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1835,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1912,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(forward_subsumption_resolution,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1907,c_1863]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_3002,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1848,c_1912]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_3422,plain,
% 3.01/1.05      ( k3_funct_2(k2_struct_0(sK1),k2_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1845,c_3002]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_4767,plain,
% 3.01/1.05      ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(demodulation,[status(thm)],[c_2851,c_3422]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_7,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 3.01/1.05      | ~ m1_subset_1(X3,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 3.01/1.05      | ~ l1_orders_2(X2)
% 3.01/1.05      | v2_struct_0(X2)
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.01/1.05      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1024,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 3.01/1.05      | ~ m1_subset_1(X3,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 3.01/1.05      | v2_struct_0(X2)
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 3.01/1.05      | sK1 != X2 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_773]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1025,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X2,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.01/1.05      | v2_struct_0(sK1)
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_1024]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1029,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.01/1.05      | ~ m1_subset_1(X2,X1)
% 3.01/1.05      | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1025,c_28,c_26,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1030,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X2,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.01/1.05      | v1_xboole_0(X1)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_1029]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1090,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X2,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(X1,sK1,X0,X2) = k1_funct_1(X0,X2)
% 3.01/1.05      | k2_struct_0(sK1) != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_1030,c_885]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1091,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,k2_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k2_yellow_6(k2_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_1090]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1217,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(X2)
% 3.01/1.05      | k2_yellow_6(k2_struct_0(sK1),sK1,X2,X1) = k1_funct_1(X2,X1)
% 3.01/1.05      | k4_waybel_1(sK1,X0) != X2
% 3.01/1.05      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.01/1.05      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_870,c_1091]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1218,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 3.01/1.05      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 3.01/1.05      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_1217]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1222,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1)
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1218,c_28,c_26,c_57,c_60,c_93,c_96,c_99,c_921]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1223,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0),X1) = k1_funct_1(k4_waybel_1(sK1,X0),X1) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_1222]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1523,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(X1_71,k2_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_1223]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1839,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1898,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,X0_71),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1839,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1903,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),X1_71) = k1_funct_1(k4_waybel_1(sK1,X0_71),X1_71)
% 3.01/1.05      | m1_subset_1(X1_71,k2_struct_0(sK1)) != iProver_top
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(forward_subsumption_resolution,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1898,c_1863]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2561,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,X0_71),k11_yellow_6(sK1,sK2))
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1848,c_1903]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2857,plain,
% 3.01/1.05      ( k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1845,c_2561]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_17,plain,
% 3.01/1.05      ( ~ v5_pre_topc(X0,X1,X1)
% 3.01/1.05      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 3.01/1.05      | ~ v3_yellow_6(X2,X1)
% 3.01/1.05      | ~ l1_waybel_0(X2,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | ~ v3_orders_2(X1)
% 3.01/1.05      | ~ l1_waybel_9(X1)
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v8_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X2)
% 3.01/1.05      | ~ v4_orders_2(X1)
% 3.01/1.05      | ~ v7_waybel_0(X2)
% 3.01/1.05      | ~ v5_orders_2(X1)
% 3.01/1.05      | ~ v2_lattice3(X1)
% 3.01/1.05      | ~ v1_lattice3(X1)
% 3.01/1.05      | v2_struct_0(X2)
% 3.01/1.05      | ~ v1_funct_1(X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_19,negated_conjecture,
% 3.01/1.05      ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_598,plain,
% 3.01/1.05      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 3.01/1.05      | ~ v3_yellow_6(X2,X1)
% 3.01/1.05      | ~ l1_waybel_0(X2,X1)
% 3.01/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 3.01/1.05      | ~ v3_orders_2(X1)
% 3.01/1.05      | ~ l1_waybel_9(X1)
% 3.01/1.05      | ~ v2_pre_topc(X1)
% 3.01/1.05      | ~ v8_pre_topc(X1)
% 3.01/1.05      | ~ v4_orders_2(X1)
% 3.01/1.05      | ~ v4_orders_2(X2)
% 3.01/1.05      | ~ v7_waybel_0(X2)
% 3.01/1.05      | ~ v5_orders_2(X1)
% 3.01/1.05      | ~ v2_lattice3(X1)
% 3.01/1.05      | ~ v1_lattice3(X1)
% 3.01/1.05      | v2_struct_0(X2)
% 3.01/1.05      | ~ v1_funct_1(X0)
% 3.01/1.05      | k4_waybel_1(sK1,sK3) != X0
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_599,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 3.01/1.05      | ~ v3_yellow_6(X0,sK1)
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v3_orders_2(sK1)
% 3.01/1.05      | ~ l1_waybel_9(sK1)
% 3.01/1.05      | ~ v2_pre_topc(sK1)
% 3.01/1.05      | ~ v8_pre_topc(sK1)
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v4_orders_2(sK1)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | ~ v5_orders_2(sK1)
% 3.01/1.05      | ~ v2_lattice3(sK1)
% 3.01/1.05      | ~ v1_lattice3(sK1)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_598]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_31,negated_conjecture,
% 3.01/1.05      ( v3_orders_2(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_30,negated_conjecture,
% 3.01/1.05      ( v4_orders_2(sK1) ),
% 3.01/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_603,plain,
% 3.01/1.05      ( ~ v7_waybel_0(X0)
% 3.01/1.05      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 3.01/1.05      | ~ v3_yellow_6(X0,sK1)
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_599,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_604,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 3.01/1.05      | ~ v3_yellow_6(X0,sK1)
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_603]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_793,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 3.01/1.05      | ~ l1_waybel_0(X0,sK1)
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v4_orders_2(X0)
% 3.01/1.05      | ~ v7_waybel_0(X0)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 3.01/1.05      | sK2 != X0
% 3.01/1.05      | sK1 != sK1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_22,c_604]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_794,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ l1_waybel_0(sK2,sK1)
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v4_orders_2(sK2)
% 3.01/1.05      | ~ v7_waybel_0(sK2)
% 3.01/1.05      | v2_struct_0(sK2)
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_793]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_796,plain,
% 3.01/1.05      ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_794,c_25,c_24,c_23,c_21]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_797,plain,
% 3.01/1.05      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 3.01/1.05      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 3.01/1.05      inference(renaming,[status(thm)],[c_796]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1144,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 3.01/1.05      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
% 3.01/1.05      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_797,c_870]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1375,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 3.01/1.05      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
% 3.01/1.05      inference(equality_resolution_simp,[status(thm)],[c_1144]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1521,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 3.01/1.05      | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_1375]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1536,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 3.01/1.05      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 3.01/1.05      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 3.01/1.05      | sP0_iProver_split ),
% 3.01/1.05      inference(splitting,
% 3.01/1.05                [splitting(split),new_symbols(definition,[])],
% 3.01/1.05                [c_1521]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1841,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 3.01/1.05      | sP0_iProver_split = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1916,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 3.01/1.05      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) != iProver_top
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 3.01/1.05      | sP0_iProver_split = iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1841,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_47,plain,
% 3.01/1.05      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1557,plain,
% 3.01/1.05      ( X0_71 != X1_71
% 3.01/1.05      | k4_waybel_1(X0_70,X0_71) = k4_waybel_1(X0_70,X1_71) ),
% 3.01/1.05      theory(equality) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1572,plain,
% 3.01/1.05      ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3) | sK3 != sK3 ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1557]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1541,plain,( X0_71 = X0_71 ),theory(equality) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1582,plain,
% 3.01/1.05      ( sK3 = sK3 ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1541]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1528,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,X0_71)) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_925]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1594,plain,
% 3.01/1.05      ( m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,X0_71)) = iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1596,plain,
% 3.01/1.05      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1535,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
% 3.01/1.05      | ~ sP0_iProver_split ),
% 3.01/1.05      inference(splitting,
% 3.01/1.05                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.01/1.05                [c_1521]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1616,plain,
% 3.01/1.05      ( k4_waybel_1(sK1,X0_71) != k4_waybel_1(sK1,sK3)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | sP0_iProver_split != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1535]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1618,plain,
% 3.01/1.05      ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
% 3.01/1.05      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 3.01/1.05      | sP0_iProver_split != iProver_top ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1616]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1963,plain,
% 3.01/1.05      ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK1)))) = iProver_top
% 3.01/1.05      | m1_subset_1(sK3,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(instantiation,[status(thm)],[c_1863]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2422,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_1916,c_47,c_1572,c_1582,c_1596,c_1618,c_1963,c_1845]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_16,plain,
% 3.01/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.01/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | v2_struct_0(X0)
% 3.01/1.05      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
% 3.01/1.05      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_843,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.01/1.05      | ~ l1_orders_2(X1)
% 3.01/1.05      | v2_struct_0(X2)
% 3.01/1.05      | v2_struct_0(X1)
% 3.01/1.05      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
% 3.01/1.05      | sK2 != X2
% 3.01/1.05      | sK1 != X1 ),
% 3.01/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_844,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | ~ l1_orders_2(sK1)
% 3.01/1.05      | v2_struct_0(sK2)
% 3.01/1.05      | v2_struct_0(sK1)
% 3.01/1.05      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 3.01/1.05      inference(unflattening,[status(thm)],[c_843]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_848,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.01/1.05      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 3.01/1.05      inference(global_propositional_subsumption,
% 3.01/1.05                [status(thm)],
% 3.01/1.05                [c_844,c_28,c_26,c_25,c_60,c_93]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1529,plain,
% 3.01/1.05      ( ~ m1_subset_1(X0_71,u1_struct_0(sK1))
% 3.01/1.05      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2) ),
% 3.01/1.05      inference(subtyping,[status(esa)],[c_848]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1833,plain,
% 3.01/1.05      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
% 3.01/1.05      | m1_subset_1(X0_71,u1_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_1858,plain,
% 3.01/1.05      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_71),sK2) = k3_waybel_2(sK1,X0_71,sK2)
% 3.01/1.05      | m1_subset_1(X0_71,k2_struct_0(sK1)) != iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_1833,c_1531]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2021,plain,
% 3.01/1.05      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
% 3.01/1.05      inference(superposition,[status(thm)],[c_1845,c_1858]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2426,plain,
% 3.01/1.05      ( r2_hidden(k2_yellow_6(k2_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 3.01/1.05      inference(light_normalisation,[status(thm)],[c_2422,c_2021]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_2940,plain,
% 3.01/1.05      ( r2_hidden(k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 3.01/1.05      inference(demodulation,[status(thm)],[c_2857,c_2426]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_5745,plain,
% 3.01/1.05      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 3.01/1.05      inference(demodulation,[status(thm)],[c_4767,c_2940]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_18,negated_conjecture,
% 3.01/1.05      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 3.01/1.05      inference(cnf_transformation,[],[f82]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(c_49,plain,
% 3.01/1.05      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
% 3.01/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/1.05  
% 3.01/1.05  cnf(contradiction,plain,
% 3.01/1.05      ( $false ),
% 3.01/1.05      inference(minisat,[status(thm)],[c_5745,c_49]) ).
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.05  
% 3.01/1.05  ------                               Statistics
% 3.01/1.05  
% 3.01/1.05  ------ General
% 3.01/1.05  
% 3.01/1.05  abstr_ref_over_cycles:                  0
% 3.01/1.05  abstr_ref_under_cycles:                 0
% 3.01/1.05  gc_basic_clause_elim:                   0
% 3.01/1.05  forced_gc_time:                         0
% 3.01/1.05  parsing_time:                           0.016
% 3.01/1.05  unif_index_cands_time:                  0.
% 3.01/1.05  unif_index_add_time:                    0.
% 3.01/1.05  orderings_time:                         0.
% 3.01/1.05  out_proof_time:                         0.014
% 3.01/1.05  total_time:                             0.258
% 3.01/1.05  num_of_symbols:                         76
% 3.01/1.05  num_of_terms:                           3868
% 3.01/1.05  
% 3.01/1.05  ------ Preprocessing
% 3.01/1.05  
% 3.01/1.05  num_of_splits:                          1
% 3.01/1.05  num_of_split_atoms:                     1
% 3.01/1.05  num_of_reused_defs:                     0
% 3.01/1.05  num_eq_ax_congr_red:                    37
% 3.01/1.05  num_of_sem_filtered_clauses:            4
% 3.01/1.05  num_of_subtypes:                        8
% 3.01/1.05  monotx_restored_types:                  0
% 3.01/1.05  sat_num_of_epr_types:                   0
% 3.01/1.05  sat_num_of_non_cyclic_types:            0
% 3.01/1.05  sat_guarded_non_collapsed_types:        0
% 3.01/1.05  num_pure_diseq_elim:                    0
% 3.01/1.05  simp_replaced_by:                       0
% 3.01/1.05  res_preprocessed:                       126
% 3.01/1.05  prep_upred:                             0
% 3.01/1.05  prep_unflattend:                        29
% 3.01/1.05  smt_new_axioms:                         0
% 3.01/1.05  pred_elim_cands:                        3
% 3.01/1.05  pred_elim:                              18
% 3.01/1.05  pred_elim_cl:                           20
% 3.01/1.05  pred_elim_cycles:                       26
% 3.01/1.05  merged_defs:                            0
% 3.01/1.05  merged_defs_ncl:                        0
% 3.01/1.05  bin_hyper_res:                          0
% 3.01/1.05  prep_cycles:                            4
% 3.01/1.05  pred_elim_time:                         0.027
% 3.01/1.05  splitting_time:                         0.
% 3.01/1.05  sem_filter_time:                        0.
% 3.01/1.05  monotx_time:                            0.
% 3.01/1.05  subtype_inf_time:                       0.
% 3.01/1.05  
% 3.01/1.05  ------ Problem properties
% 3.01/1.05  
% 3.01/1.05  clauses:                                15
% 3.01/1.05  conjectures:                            2
% 3.01/1.05  epr:                                    0
% 3.01/1.05  horn:                                   13
% 3.01/1.05  ground:                                 5
% 3.01/1.05  unary:                                  4
% 3.01/1.05  binary:                                 3
% 3.01/1.05  lits:                                   39
% 3.01/1.05  lits_eq:                                10
% 3.01/1.05  fd_pure:                                0
% 3.01/1.05  fd_pseudo:                              0
% 3.01/1.05  fd_cond:                                0
% 3.01/1.05  fd_pseudo_cond:                         0
% 3.01/1.05  ac_symbols:                             0
% 3.01/1.05  
% 3.01/1.05  ------ Propositional Solver
% 3.01/1.05  
% 3.01/1.05  prop_solver_calls:                      32
% 3.01/1.05  prop_fast_solver_calls:                 1158
% 3.01/1.05  smt_solver_calls:                       0
% 3.01/1.05  smt_fast_solver_calls:                  0
% 3.01/1.05  prop_num_of_clauses:                    1372
% 3.01/1.05  prop_preprocess_simplified:             4466
% 3.01/1.05  prop_fo_subsumed:                       50
% 3.01/1.05  prop_solver_time:                       0.
% 3.01/1.05  smt_solver_time:                        0.
% 3.01/1.05  smt_fast_solver_time:                   0.
% 3.01/1.05  prop_fast_solver_time:                  0.
% 3.01/1.05  prop_unsat_core_time:                   0.
% 3.01/1.05  
% 3.01/1.05  ------ QBF
% 3.01/1.05  
% 3.01/1.05  qbf_q_res:                              0
% 3.01/1.05  qbf_num_tautologies:                    0
% 3.01/1.05  qbf_prep_cycles:                        0
% 3.01/1.05  
% 3.01/1.05  ------ BMC1
% 3.01/1.05  
% 3.01/1.05  bmc1_current_bound:                     -1
% 3.01/1.05  bmc1_last_solved_bound:                 -1
% 3.01/1.05  bmc1_unsat_core_size:                   -1
% 3.01/1.05  bmc1_unsat_core_parents_size:           -1
% 3.01/1.05  bmc1_merge_next_fun:                    0
% 3.01/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.05  
% 3.01/1.05  ------ Instantiation
% 3.01/1.05  
% 3.01/1.05  inst_num_of_clauses:                    468
% 3.01/1.05  inst_num_in_passive:                    34
% 3.01/1.05  inst_num_in_active:                     372
% 3.01/1.05  inst_num_in_unprocessed:                62
% 3.01/1.05  inst_num_of_loops:                      390
% 3.01/1.05  inst_num_of_learning_restarts:          0
% 3.01/1.05  inst_num_moves_active_passive:          9
% 3.01/1.05  inst_lit_activity:                      0
% 3.01/1.05  inst_lit_activity_moves:                0
% 3.01/1.05  inst_num_tautologies:                   0
% 3.01/1.05  inst_num_prop_implied:                  0
% 3.01/1.05  inst_num_existing_simplified:           0
% 3.01/1.05  inst_num_eq_res_simplified:             0
% 3.01/1.05  inst_num_child_elim:                    0
% 3.01/1.05  inst_num_of_dismatching_blockings:      142
% 3.01/1.05  inst_num_of_non_proper_insts:           740
% 3.01/1.05  inst_num_of_duplicates:                 0
% 3.01/1.05  inst_inst_num_from_inst_to_res:         0
% 3.01/1.05  inst_dismatching_checking_time:         0.
% 3.01/1.05  
% 3.01/1.05  ------ Resolution
% 3.01/1.05  
% 3.01/1.05  res_num_of_clauses:                     0
% 3.01/1.05  res_num_in_passive:                     0
% 3.01/1.05  res_num_in_active:                      0
% 3.01/1.05  res_num_of_loops:                       130
% 3.01/1.05  res_forward_subset_subsumed:            191
% 3.01/1.05  res_backward_subset_subsumed:           2
% 3.01/1.05  res_forward_subsumed:                   0
% 3.01/1.05  res_backward_subsumed:                  0
% 3.01/1.05  res_forward_subsumption_resolution:     4
% 3.01/1.05  res_backward_subsumption_resolution:    2
% 3.01/1.05  res_clause_to_clause_subsumption:       499
% 3.01/1.05  res_orphan_elimination:                 0
% 3.01/1.05  res_tautology_del:                      162
% 3.01/1.05  res_num_eq_res_simplified:              1
% 3.01/1.05  res_num_sel_changes:                    0
% 3.01/1.05  res_moves_from_active_to_pass:          0
% 3.01/1.05  
% 3.01/1.05  ------ Superposition
% 3.01/1.05  
% 3.01/1.05  sup_time_total:                         0.
% 3.01/1.05  sup_time_generating:                    0.
% 3.01/1.05  sup_time_sim_full:                      0.
% 3.01/1.05  sup_time_sim_immed:                     0.
% 3.01/1.05  
% 3.01/1.05  sup_num_of_clauses:                     107
% 3.01/1.05  sup_num_in_active:                      70
% 3.01/1.05  sup_num_in_passive:                     37
% 3.01/1.05  sup_num_of_loops:                       76
% 3.01/1.05  sup_fw_superposition:                   97
% 3.01/1.05  sup_bw_superposition:                   7
% 3.01/1.05  sup_immediate_simplified:               4
% 3.01/1.05  sup_given_eliminated:                   0
% 3.01/1.05  comparisons_done:                       0
% 3.01/1.05  comparisons_avoided:                    70
% 3.01/1.05  
% 3.01/1.05  ------ Simplifications
% 3.01/1.05  
% 3.01/1.05  
% 3.01/1.05  sim_fw_subset_subsumed:                 0
% 3.01/1.05  sim_bw_subset_subsumed:                 0
% 3.01/1.05  sim_fw_subsumed:                        0
% 3.01/1.05  sim_bw_subsumed:                        0
% 3.01/1.05  sim_fw_subsumption_res:                 2
% 3.01/1.05  sim_bw_subsumption_res:                 0
% 3.01/1.05  sim_tautology_del:                      0
% 3.01/1.05  sim_eq_tautology_del:                   11
% 3.01/1.05  sim_eq_res_simp:                        0
% 3.01/1.05  sim_fw_demodulated:                     0
% 3.01/1.05  sim_bw_demodulated:                     6
% 3.01/1.05  sim_light_normalised:                   18
% 3.01/1.05  sim_joinable_taut:                      0
% 3.01/1.05  sim_joinable_simp:                      0
% 3.01/1.05  sim_ac_normalised:                      0
% 3.01/1.05  sim_smt_subsumption:                    0
% 3.01/1.05  
%------------------------------------------------------------------------------
