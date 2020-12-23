%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:54 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  228 (2194 expanded)
%              Number of clauses        :  150 ( 544 expanded)
%              Number of leaves         :   19 ( 677 expanded)
%              Depth                    :   25
%              Number of atoms          : 1086 (22527 expanded)
%              Number of equality atoms :  171 ( 231 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   32 (   4 average)
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
            ( ( l1_waybel_0(X1,X0)
              & v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                 => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
          & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1)))
        & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f45,f44,f43])).

fof(f75,plain,(
    v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f61,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f52,plain,(
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

fof(f7,axiom,(
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

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( ~ v5_pre_topc(X0,X1,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
    | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v3_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_594,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
    | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v3_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_waybel_9(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k4_waybel_1(sK1,sK3) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_595,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v3_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(X0)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_599,plain,
    ( ~ v4_orders_2(X0)
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).

cnf(c_600,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_599])).

cnf(c_858,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_600])).

cnf(c_859,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_861,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_24,c_23,c_22,c_20])).

cnf(c_862,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_861])).

cnf(c_11,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_774,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_775,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_929,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_775])).

cnf(c_930,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_59,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_89,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_26,c_25,c_59,c_89])).

cnf(c_935,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1138,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_862,c_935])).

cnf(c_1363,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_1138])).

cnf(c_1508,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_1363])).

cnf(c_1522,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1508])).

cnf(c_1818,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1538,plain,
    ( X0_70 != X1_70
    | k4_waybel_1(X0_69,X0_70) = k4_waybel_1(X0_69,X1_70) ),
    theory(equality)).

cnf(c_1551,plain,
    ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_1526,plain,
    ( X0_70 = X0_70 ),
    theory(equality)).

cnf(c_1560,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1001,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_775])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_1001])).

cnf(c_1006,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1002,c_26,c_25,c_59,c_89])).

cnf(c_1515,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0_70)) ),
    inference(subtyping,[status(esa)],[c_1006])).

cnf(c_1571,plain,
    ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,X0_70)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_1573,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_775])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1023])).

cnf(c_1028,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1024,c_26,c_25,c_59,c_89])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_1028])).

cnf(c_1514,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_1029])).

cnf(c_1574,plain,
    ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1576,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_1592,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_1521,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1508])).

cnf(c_1593,plain,
    ( k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_1595,plain,
    ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_3831,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1818,c_46,c_1551,c_1560,c_1573,c_1576,c_1592,c_1595])).

cnf(c_1519,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1807,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_909,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_26,c_25,c_24,c_59,c_89])).

cnf(c_1516,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2) ),
    inference(subtyping,[status(esa)],[c_913])).

cnf(c_1810,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_1945,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1807,c_1810])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_405,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_5])).

cnf(c_406,plain,
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
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_726,plain,
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
    inference(resolution_lifted,[status(thm)],[c_406,c_31])).

cnf(c_727,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v3_yellow_6(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_32,c_26,c_25,c_59,c_89])).

cnf(c_732,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_731])).

cnf(c_847,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_732])).

cnf(c_848,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_850,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_24,c_23,c_22,c_20])).

cnf(c_1517,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_850])).

cnf(c_1809,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1517])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_373,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_391,plain,
    ( ~ l1_waybel_9(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_14,c_373])).

cnf(c_763,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_391,c_25])).

cnf(c_764,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_56,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_92,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_95,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_766,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_26,c_25,c_56,c_59,c_89,c_92,c_95])).

cnf(c_785,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_766])).

cnf(c_786,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_947,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_786,c_775])).

cnf(c_948,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_26,c_25,c_59,c_89])).

cnf(c_953,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X2)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X2,X0) = k1_funct_1(X2,X0)
    | k4_waybel_1(sK1,X1) != X2
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_935,c_953])).

cnf(c_1234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_1248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1234,c_1006,c_1029])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
    inference(subtyping,[status(esa)],[c_1248])).

cnf(c_1817,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_3034,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1817])).

cnf(c_3141,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1809,c_3034])).

cnf(c_9,plain,
    ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_974,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_775])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_26,c_25,c_59,c_89])).

cnf(c_980,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1006,c_980])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1029,c_1018])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70) ),
    inference(subtyping,[status(esa)],[c_1040])).

cnf(c_1813,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_2379,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k11_lattice3(sK1,sK3,X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1813])).

cnf(c_2397,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1809,c_2379])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_28])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_26,c_25,c_59])).

cnf(c_1518,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70) ),
    inference(subtyping,[status(esa)],[c_648])).

cnf(c_1808,plain,
    ( k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1956,plain,
    ( k11_lattice3(sK1,sK3,X0_70) = k12_lattice3(sK1,sK3,X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1808])).

cnf(c_2003,plain,
    ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1809,c_1956])).

cnf(c_2399,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2397,c_2003])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_812,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_766])).

cnf(c_813,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X3)))
    | ~ v1_funct_1(X2)
    | k3_funct_2(u1_struct_0(sK1),X3,X2,X0) = k1_funct_1(X2,X0)
    | k4_waybel_1(sK1,X1) != X2
    | u1_struct_0(sK1) != X3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_813,c_935])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1161])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1162,c_1006,c_1029])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
    inference(subtyping,[status(esa)],[c_1176])).

cnf(c_1814,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_2450,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1814])).

cnf(c_2545,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1809,c_2450])).

cnf(c_2627,plain,
    ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2399,c_2545])).

cnf(c_3143,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3141,c_2627])).

cnf(c_3835,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3831,c_1945,c_3143])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1520,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1806,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_3837,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3835,c_1806])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.36/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.99  
% 2.36/0.99  ------  iProver source info
% 2.36/0.99  
% 2.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.99  git: non_committed_changes: false
% 2.36/0.99  git: last_make_outside_of_git: false
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/0.99  --bmc1_symbol_reachability              true
% 2.36/0.99  --bmc1_property_lemmas                  false
% 2.36/0.99  --bmc1_k_induction                      false
% 2.36/0.99  --bmc1_non_equiv_states                 false
% 2.36/0.99  --bmc1_deadlock                         false
% 2.36/0.99  --bmc1_ucm                              false
% 2.36/0.99  --bmc1_add_unsat_core                   none
% 2.36/0.99  --bmc1_unsat_core_children              false
% 2.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.99  --bmc1_out_stat                         full
% 2.36/0.99  --bmc1_ground_init                      false
% 2.36/0.99  --bmc1_pre_inst_next_state              false
% 2.36/0.99  --bmc1_pre_inst_state                   false
% 2.36/0.99  --bmc1_pre_inst_reach_state             false
% 2.36/0.99  --bmc1_out_unsat_core                   false
% 2.36/0.99  --bmc1_aig_witness_out                  false
% 2.36/0.99  --bmc1_verbose                          false
% 2.36/0.99  --bmc1_dump_clauses_tptp                false
% 2.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.99  --bmc1_dump_file                        -
% 2.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.99  --bmc1_ucm_extend_mode                  1
% 2.36/0.99  --bmc1_ucm_init_mode                    2
% 2.36/0.99  --bmc1_ucm_cone_mode                    none
% 2.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.99  --bmc1_ucm_relax_model                  4
% 2.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.99  --bmc1_ucm_layered_model                none
% 2.36/0.99  --bmc1_ucm_max_lemma_size               10
% 2.36/0.99  
% 2.36/0.99  ------ AIG Options
% 2.36/0.99  
% 2.36/0.99  --aig_mode                              false
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation Options
% 2.36/0.99  
% 2.36/0.99  --instantiation_flag                    true
% 2.36/0.99  --inst_sos_flag                         false
% 2.36/0.99  --inst_sos_phase                        true
% 2.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel_side                     num_symb
% 2.36/0.99  --inst_solver_per_active                1400
% 2.36/0.99  --inst_solver_calls_frac                1.
% 2.36/0.99  --inst_passive_queue_type               priority_queues
% 2.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.99  --inst_passive_queues_freq              [25;2]
% 2.36/0.99  --inst_dismatching                      true
% 2.36/0.99  --inst_eager_unprocessed_to_passive     true
% 2.36/0.99  --inst_prop_sim_given                   true
% 2.36/0.99  --inst_prop_sim_new                     false
% 2.36/0.99  --inst_subs_new                         false
% 2.36/0.99  --inst_eq_res_simp                      false
% 2.36/0.99  --inst_subs_given                       false
% 2.36/0.99  --inst_orphan_elimination               true
% 2.36/0.99  --inst_learning_loop_flag               true
% 2.36/0.99  --inst_learning_start                   3000
% 2.36/0.99  --inst_learning_factor                  2
% 2.36/0.99  --inst_start_prop_sim_after_learn       3
% 2.36/0.99  --inst_sel_renew                        solver
% 2.36/0.99  --inst_lit_activity_flag                true
% 2.36/0.99  --inst_restr_to_given                   false
% 2.36/0.99  --inst_activity_threshold               500
% 2.36/0.99  --inst_out_proof                        true
% 2.36/0.99  
% 2.36/0.99  ------ Resolution Options
% 2.36/0.99  
% 2.36/0.99  --resolution_flag                       true
% 2.36/0.99  --res_lit_sel                           adaptive
% 2.36/0.99  --res_lit_sel_side                      none
% 2.36/0.99  --res_ordering                          kbo
% 2.36/0.99  --res_to_prop_solver                    active
% 2.36/0.99  --res_prop_simpl_new                    false
% 2.36/0.99  --res_prop_simpl_given                  true
% 2.36/0.99  --res_passive_queue_type                priority_queues
% 2.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.99  --res_passive_queues_freq               [15;5]
% 2.36/0.99  --res_forward_subs                      full
% 2.36/0.99  --res_backward_subs                     full
% 2.36/0.99  --res_forward_subs_resolution           true
% 2.36/0.99  --res_backward_subs_resolution          true
% 2.36/0.99  --res_orphan_elimination                true
% 2.36/0.99  --res_time_limit                        2.
% 2.36/0.99  --res_out_proof                         true
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Options
% 2.36/0.99  
% 2.36/0.99  --superposition_flag                    true
% 2.36/0.99  --sup_passive_queue_type                priority_queues
% 2.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.99  --demod_completeness_check              fast
% 2.36/0.99  --demod_use_ground                      true
% 2.36/0.99  --sup_to_prop_solver                    passive
% 2.36/0.99  --sup_prop_simpl_new                    true
% 2.36/0.99  --sup_prop_simpl_given                  true
% 2.36/0.99  --sup_fun_splitting                     false
% 2.36/0.99  --sup_smt_interval                      50000
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Simplification Setup
% 2.36/0.99  
% 2.36/0.99  --sup_indices_passive                   []
% 2.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_full_bw                           [BwDemod]
% 2.36/0.99  --sup_immed_triv                        [TrivRules]
% 2.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_immed_bw_main                     []
% 2.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  
% 2.36/0.99  ------ Combination Options
% 2.36/0.99  
% 2.36/0.99  --comb_res_mult                         3
% 2.36/0.99  --comb_sup_mult                         2
% 2.36/0.99  --comb_inst_mult                        10
% 2.36/0.99  
% 2.36/0.99  ------ Debug Options
% 2.36/0.99  
% 2.36/0.99  --dbg_backtrace                         false
% 2.36/0.99  --dbg_dump_prop_clauses                 false
% 2.36/0.99  --dbg_dump_prop_clauses_file            -
% 2.36/0.99  --dbg_out_stat                          false
% 2.36/0.99  ------ Parsing...
% 2.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.99  ------ Proving...
% 2.36/0.99  ------ Problem Properties 
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  clauses                                 14
% 2.36/0.99  conjectures                             2
% 2.36/0.99  EPR                                     0
% 2.36/0.99  Horn                                    12
% 2.36/0.99  unary                                   3
% 2.36/0.99  binary                                  3
% 2.36/0.99  lits                                    36
% 2.36/0.99  lits eq                                 9
% 2.36/0.99  fd_pure                                 0
% 2.36/0.99  fd_pseudo                               0
% 2.36/0.99  fd_cond                                 0
% 2.36/0.99  fd_pseudo_cond                          0
% 2.36/0.99  AC symbols                              0
% 2.36/0.99  
% 2.36/0.99  ------ Schedule dynamic 5 is on 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  Current options:
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/0.99  --bmc1_symbol_reachability              true
% 2.36/0.99  --bmc1_property_lemmas                  false
% 2.36/0.99  --bmc1_k_induction                      false
% 2.36/0.99  --bmc1_non_equiv_states                 false
% 2.36/0.99  --bmc1_deadlock                         false
% 2.36/0.99  --bmc1_ucm                              false
% 2.36/0.99  --bmc1_add_unsat_core                   none
% 2.36/0.99  --bmc1_unsat_core_children              false
% 2.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.99  --bmc1_out_stat                         full
% 2.36/0.99  --bmc1_ground_init                      false
% 2.36/0.99  --bmc1_pre_inst_next_state              false
% 2.36/0.99  --bmc1_pre_inst_state                   false
% 2.36/0.99  --bmc1_pre_inst_reach_state             false
% 2.36/0.99  --bmc1_out_unsat_core                   false
% 2.36/0.99  --bmc1_aig_witness_out                  false
% 2.36/0.99  --bmc1_verbose                          false
% 2.36/0.99  --bmc1_dump_clauses_tptp                false
% 2.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.99  --bmc1_dump_file                        -
% 2.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.99  --bmc1_ucm_extend_mode                  1
% 2.36/0.99  --bmc1_ucm_init_mode                    2
% 2.36/0.99  --bmc1_ucm_cone_mode                    none
% 2.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.99  --bmc1_ucm_relax_model                  4
% 2.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.99  --bmc1_ucm_layered_model                none
% 2.36/0.99  --bmc1_ucm_max_lemma_size               10
% 2.36/0.99  
% 2.36/0.99  ------ AIG Options
% 2.36/0.99  
% 2.36/0.99  --aig_mode                              false
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation Options
% 2.36/0.99  
% 2.36/0.99  --instantiation_flag                    true
% 2.36/0.99  --inst_sos_flag                         false
% 2.36/0.99  --inst_sos_phase                        true
% 2.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel_side                     none
% 2.36/0.99  --inst_solver_per_active                1400
% 2.36/0.99  --inst_solver_calls_frac                1.
% 2.36/0.99  --inst_passive_queue_type               priority_queues
% 2.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.99  --inst_passive_queues_freq              [25;2]
% 2.36/0.99  --inst_dismatching                      true
% 2.36/0.99  --inst_eager_unprocessed_to_passive     true
% 2.36/0.99  --inst_prop_sim_given                   true
% 2.36/0.99  --inst_prop_sim_new                     false
% 2.36/0.99  --inst_subs_new                         false
% 2.36/0.99  --inst_eq_res_simp                      false
% 2.36/0.99  --inst_subs_given                       false
% 2.36/0.99  --inst_orphan_elimination               true
% 2.36/0.99  --inst_learning_loop_flag               true
% 2.36/0.99  --inst_learning_start                   3000
% 2.36/0.99  --inst_learning_factor                  2
% 2.36/0.99  --inst_start_prop_sim_after_learn       3
% 2.36/0.99  --inst_sel_renew                        solver
% 2.36/0.99  --inst_lit_activity_flag                true
% 2.36/0.99  --inst_restr_to_given                   false
% 2.36/0.99  --inst_activity_threshold               500
% 2.36/0.99  --inst_out_proof                        true
% 2.36/0.99  
% 2.36/0.99  ------ Resolution Options
% 2.36/0.99  
% 2.36/0.99  --resolution_flag                       false
% 2.36/0.99  --res_lit_sel                           adaptive
% 2.36/0.99  --res_lit_sel_side                      none
% 2.36/0.99  --res_ordering                          kbo
% 2.36/0.99  --res_to_prop_solver                    active
% 2.36/0.99  --res_prop_simpl_new                    false
% 2.36/0.99  --res_prop_simpl_given                  true
% 2.36/0.99  --res_passive_queue_type                priority_queues
% 2.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.99  --res_passive_queues_freq               [15;5]
% 2.36/0.99  --res_forward_subs                      full
% 2.36/0.99  --res_backward_subs                     full
% 2.36/0.99  --res_forward_subs_resolution           true
% 2.36/0.99  --res_backward_subs_resolution          true
% 2.36/0.99  --res_orphan_elimination                true
% 2.36/0.99  --res_time_limit                        2.
% 2.36/0.99  --res_out_proof                         true
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Options
% 2.36/0.99  
% 2.36/0.99  --superposition_flag                    true
% 2.36/0.99  --sup_passive_queue_type                priority_queues
% 2.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.99  --demod_completeness_check              fast
% 2.36/0.99  --demod_use_ground                      true
% 2.36/0.99  --sup_to_prop_solver                    passive
% 2.36/0.99  --sup_prop_simpl_new                    true
% 2.36/0.99  --sup_prop_simpl_given                  true
% 2.36/0.99  --sup_fun_splitting                     false
% 2.36/0.99  --sup_smt_interval                      50000
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Simplification Setup
% 2.36/0.99  
% 2.36/0.99  --sup_indices_passive                   []
% 2.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_full_bw                           [BwDemod]
% 2.36/0.99  --sup_immed_triv                        [TrivRules]
% 2.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_immed_bw_main                     []
% 2.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  
% 2.36/0.99  ------ Combination Options
% 2.36/0.99  
% 2.36/0.99  --comb_res_mult                         3
% 2.36/0.99  --comb_sup_mult                         2
% 2.36/0.99  --comb_inst_mult                        10
% 2.36/0.99  
% 2.36/0.99  ------ Debug Options
% 2.36/0.99  
% 2.36/0.99  --dbg_backtrace                         false
% 2.36/0.99  --dbg_dump_prop_clauses                 false
% 2.36/0.99  --dbg_dump_prop_clauses_file            -
% 2.36/0.99  --dbg_out_stat                          false
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  ------ Proving...
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  % SZS status Theorem for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99   Resolution empty clause
% 2.36/0.99  
% 2.36/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  fof(f13,conjecture,(
% 2.36/0.99    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f14,negated_conjecture,(
% 2.36/0.99    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.36/0.99    inference(negated_conjecture,[],[f13])).
% 2.36/0.99  
% 2.36/0.99  fof(f37,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f14])).
% 2.36/0.99  
% 2.36/0.99  fof(f38,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.36/0.99    inference(flattening,[],[f37])).
% 2.36/0.99  
% 2.36/0.99  fof(f45,plain,(
% 2.36/0.99    ( ! [X0,X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1))) & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f44,plain,(
% 2.36/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,sK2)),k10_yellow_6(X0,k3_waybel_2(X0,X2,sK2))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2,X0) & v3_yellow_6(sK2,X0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f43,plain,(
% 2.36/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK1,X2,k11_yellow_6(sK1,X1)),k10_yellow_6(sK1,k3_waybel_2(sK1,X2,X1))) & v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(X1,sK1) & v3_yellow_6(X1,sK1) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f46,plain,(
% 2.36/0.99    ((~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) & v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) & m1_subset_1(sK3,u1_struct_0(sK1))) & l1_waybel_0(sK2,sK1) & v3_yellow_6(sK2,sK1) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f45,f44,f43])).
% 2.36/0.99  
% 2.36/0.99  fof(f75,plain,(
% 2.36/0.99    v3_yellow_6(sK2,sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f12,axiom,(
% 2.36/0.99    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f35,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f12])).
% 2.36/0.99  
% 2.36/0.99  fof(f36,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.99    inference(flattening,[],[f35])).
% 2.36/0.99  
% 2.36/0.99  fof(f63,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f36])).
% 2.36/0.99  
% 2.36/0.99  fof(f78,plain,(
% 2.36/0.99    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f64,plain,(
% 2.36/0.99    v2_pre_topc(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f65,plain,(
% 2.36/0.99    v8_pre_topc(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f66,plain,(
% 2.36/0.99    v3_orders_2(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f67,plain,(
% 2.36/0.99    v4_orders_2(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f68,plain,(
% 2.36/0.99    v5_orders_2(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f69,plain,(
% 2.36/0.99    v1_lattice3(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f70,plain,(
% 2.36/0.99    v2_lattice3(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f71,plain,(
% 2.36/0.99    l1_waybel_9(sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f72,plain,(
% 2.36/0.99    ~v2_struct_0(sK2)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f73,plain,(
% 2.36/0.99    v4_orders_2(sK2)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f74,plain,(
% 2.36/0.99    v7_waybel_0(sK2)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f76,plain,(
% 2.36/0.99    l1_waybel_0(sK2,sK1)),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f9,axiom,(
% 2.36/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f30,plain,(
% 2.36/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f9])).
% 2.36/0.99  
% 2.36/0.99  fof(f31,plain,(
% 2.36/0.99    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(flattening,[],[f30])).
% 2.36/0.99  
% 2.36/0.99  fof(f58,plain,(
% 2.36/0.99    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f31])).
% 2.36/0.99  
% 2.36/0.99  fof(f10,axiom,(
% 2.36/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f32,plain,(
% 2.36/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f10])).
% 2.36/0.99  
% 2.36/0.99  fof(f61,plain,(
% 2.36/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f32])).
% 2.36/0.99  
% 2.36/0.99  fof(f4,axiom,(
% 2.36/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f20,plain,(
% 2.36/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f4])).
% 2.36/0.99  
% 2.36/0.99  fof(f21,plain,(
% 2.36/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.36/0.99    inference(flattening,[],[f20])).
% 2.36/0.99  
% 2.36/0.99  fof(f50,plain,(
% 2.36/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f21])).
% 2.36/0.99  
% 2.36/0.99  fof(f77,plain,(
% 2.36/0.99    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  fof(f57,plain,(
% 2.36/0.99    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f31])).
% 2.36/0.99  
% 2.36/0.99  fof(f59,plain,(
% 2.36/0.99    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f31])).
% 2.36/0.99  
% 2.36/0.99  fof(f11,axiom,(
% 2.36/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f33,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f11])).
% 2.36/0.99  
% 2.36/0.99  fof(f34,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(flattening,[],[f33])).
% 2.36/0.99  
% 2.36/0.99  fof(f62,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f34])).
% 2.36/0.99  
% 2.36/0.99  fof(f60,plain,(
% 2.36/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f32])).
% 2.36/0.99  
% 2.36/0.99  fof(f6,axiom,(
% 2.36/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f24,plain,(
% 2.36/0.99    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f6])).
% 2.36/0.99  
% 2.36/0.99  fof(f25,plain,(
% 2.36/0.99    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(flattening,[],[f24])).
% 2.36/0.99  
% 2.36/0.99  fof(f52,plain,(
% 2.36/0.99    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f25])).
% 2.36/0.99  
% 2.36/0.99  fof(f7,axiom,(
% 2.36/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f26,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f7])).
% 2.36/0.99  
% 2.36/0.99  fof(f27,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f26])).
% 2.36/0.99  
% 2.36/0.99  fof(f53,plain,(
% 2.36/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f27])).
% 2.36/0.99  
% 2.36/0.99  fof(f2,axiom,(
% 2.36/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f17,plain,(
% 2.36/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.36/0.99    inference(ennf_transformation,[],[f2])).
% 2.36/0.99  
% 2.36/0.99  fof(f48,plain,(
% 2.36/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f17])).
% 2.36/0.99  
% 2.36/0.99  fof(f3,axiom,(
% 2.36/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f18,plain,(
% 2.36/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f3])).
% 2.36/0.99  
% 2.36/0.99  fof(f19,plain,(
% 2.36/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(flattening,[],[f18])).
% 2.36/0.99  
% 2.36/0.99  fof(f49,plain,(
% 2.36/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f19])).
% 2.36/0.99  
% 2.36/0.99  fof(f8,axiom,(
% 2.36/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f28,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f8])).
% 2.36/0.99  
% 2.36/0.99  fof(f29,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(flattening,[],[f28])).
% 2.36/0.99  
% 2.36/0.99  fof(f39,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(nnf_transformation,[],[f29])).
% 2.36/0.99  
% 2.36/0.99  fof(f40,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(rectify,[],[f39])).
% 2.36/0.99  
% 2.36/0.99  fof(f41,plain,(
% 2.36/0.99    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.36/0.99    introduced(choice_axiom,[])).
% 2.36/0.99  
% 2.36/0.99  fof(f42,plain,(
% 2.36/0.99    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.36/0.99  
% 2.36/0.99  fof(f54,plain,(
% 2.36/0.99    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f42])).
% 2.36/0.99  
% 2.36/0.99  fof(f80,plain,(
% 2.36/0.99    ( ! [X4,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.36/0.99    inference(equality_resolution,[],[f54])).
% 2.36/0.99  
% 2.36/0.99  fof(f5,axiom,(
% 2.36/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f22,plain,(
% 2.36/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f5])).
% 2.36/0.99  
% 2.36/0.99  fof(f23,plain,(
% 2.36/0.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.36/0.99    inference(flattening,[],[f22])).
% 2.36/0.99  
% 2.36/0.99  fof(f51,plain,(
% 2.36/0.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f23])).
% 2.36/0.99  
% 2.36/0.99  fof(f1,axiom,(
% 2.36/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/0.99  
% 2.36/0.99  fof(f15,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.36/0.99    inference(ennf_transformation,[],[f1])).
% 2.36/0.99  
% 2.36/0.99  fof(f16,plain,(
% 2.36/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.36/0.99    inference(flattening,[],[f15])).
% 2.36/0.99  
% 2.36/0.99  fof(f47,plain,(
% 2.36/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.36/0.99    inference(cnf_transformation,[],[f16])).
% 2.36/0.99  
% 2.36/0.99  fof(f79,plain,(
% 2.36/0.99    ~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2)))),
% 2.36/0.99    inference(cnf_transformation,[],[f46])).
% 2.36/0.99  
% 2.36/0.99  cnf(c_21,negated_conjecture,
% 2.36/0.99      ( v3_yellow_6(sK2,sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_16,plain,
% 2.36/0.99      ( ~ v5_pre_topc(X0,X1,X1)
% 2.36/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.36/0.99      | ~ v3_yellow_6(X2,X1)
% 2.36/0.99      | ~ l1_waybel_0(X2,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | ~ v3_orders_2(X1)
% 2.36/0.99      | ~ v1_lattice3(X1)
% 2.36/0.99      | ~ l1_waybel_9(X1)
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v8_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X2)
% 2.36/0.99      | ~ v4_orders_2(X1)
% 2.36/0.99      | ~ v7_waybel_0(X2)
% 2.36/0.99      | ~ v5_orders_2(X1)
% 2.36/0.99      | ~ v2_lattice3(X1)
% 2.36/0.99      | v2_struct_0(X2)
% 2.36/0.99      | ~ v1_funct_1(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_18,negated_conjecture,
% 2.36/0.99      ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_594,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.36/0.99      | ~ v3_yellow_6(X2,X1)
% 2.36/0.99      | ~ l1_waybel_0(X2,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | ~ v3_orders_2(X1)
% 2.36/0.99      | ~ v1_lattice3(X1)
% 2.36/0.99      | ~ l1_waybel_9(X1)
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v8_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X1)
% 2.36/0.99      | ~ v4_orders_2(X2)
% 2.36/0.99      | ~ v7_waybel_0(X2)
% 2.36/0.99      | ~ v5_orders_2(X1)
% 2.36/0.99      | ~ v2_lattice3(X1)
% 2.36/0.99      | v2_struct_0(X2)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k4_waybel_1(sK1,sK3) != X0
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_595,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.36/0.99      | ~ v3_yellow_6(X0,sK1)
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v3_orders_2(sK1)
% 2.36/0.99      | ~ v1_lattice3(sK1)
% 2.36/0.99      | ~ l1_waybel_9(sK1)
% 2.36/0.99      | ~ v2_pre_topc(sK1)
% 2.36/0.99      | ~ v8_pre_topc(sK1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v4_orders_2(sK1)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | ~ v5_orders_2(sK1)
% 2.36/0.99      | ~ v2_lattice3(sK1)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_32,negated_conjecture,
% 2.36/0.99      ( v2_pre_topc(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_31,negated_conjecture,
% 2.36/0.99      ( v8_pre_topc(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_30,negated_conjecture,
% 2.36/0.99      ( v3_orders_2(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_29,negated_conjecture,
% 2.36/0.99      ( v4_orders_2(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_28,negated_conjecture,
% 2.36/0.99      ( v5_orders_2(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_27,negated_conjecture,
% 2.36/0.99      ( v1_lattice3(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_26,negated_conjecture,
% 2.36/0.99      ( v2_lattice3(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_25,negated_conjecture,
% 2.36/0.99      ( l1_waybel_9(sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_599,plain,
% 2.36/0.99      ( ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.36/0.99      | ~ v3_yellow_6(X0,sK1)
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_595,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_600,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.36/0.99      | ~ v3_yellow_6(X0,sK1)
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_599]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_858,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.36/0.99      | sK2 != X0
% 2.36/0.99      | sK1 != sK1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_600]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_859,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ l1_waybel_0(sK2,sK1)
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v4_orders_2(sK2)
% 2.36/0.99      | ~ v7_waybel_0(sK2)
% 2.36/0.99      | v2_struct_0(sK2)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_858]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_24,negated_conjecture,
% 2.36/0.99      ( ~ v2_struct_0(sK2) ),
% 2.36/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_23,negated_conjecture,
% 2.36/0.99      ( v4_orders_2(sK2) ),
% 2.36/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_22,negated_conjecture,
% 2.36/0.99      ( v7_waybel_0(sK2) ),
% 2.36/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_20,negated_conjecture,
% 2.36/0.99      ( l1_waybel_0(sK2,sK1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_861,plain,
% 2.36/0.99      ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_859,c_24,c_23,c_22,c_20]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_862,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_861]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_11,plain,
% 2.36/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.99      | ~ l1_orders_2(X0)
% 2.36/0.99      | v2_struct_0(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_13,plain,
% 2.36/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_774,plain,
% 2.36/0.99      ( l1_orders_2(X0) | sK1 != X0 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_775,plain,
% 2.36/0.99      ( l1_orders_2(sK1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_774]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_929,plain,
% 2.36/0.99      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | sK1 != X0 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_775]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_930,plain,
% 2.36/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | v2_struct_0(sK1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_929]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_59,plain,
% 2.36/0.99      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3,plain,
% 2.36/0.99      ( ~ l1_orders_2(X0) | ~ v2_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_89,plain,
% 2.36/0.99      ( ~ l1_orders_2(sK1) | ~ v2_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_934,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_930,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_935,plain,
% 2.36/0.99      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_934]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1138,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.36/0.99      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
% 2.36/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_862,c_935]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1363,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.36/0.99      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
% 2.36/0.99      inference(equality_resolution_simp,[status(thm)],[c_1138]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1508,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.36/0.99      | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1363]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1522,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.36/0.99      | sP0_iProver_split ),
% 2.36/0.99      inference(splitting,
% 2.36/0.99                [splitting(split),new_symbols(definition,[])],
% 2.36/0.99                [c_1508]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1818,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.36/0.99      | sP0_iProver_split = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_19,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_46,plain,
% 2.36/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1538,plain,
% 2.36/0.99      ( X0_70 != X1_70 | k4_waybel_1(X0_69,X0_70) = k4_waybel_1(X0_69,X1_70) ),
% 2.36/0.99      theory(equality) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1551,plain,
% 2.36/0.99      ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3) | sK3 != sK3 ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1526,plain,( X0_70 = X0_70 ),theory(equality) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1560,plain,
% 2.36/0.99      ( sK3 = sK3 ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1526]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_12,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1001,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | v1_funct_1(k4_waybel_1(X1,X0))
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_775]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1002,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | v2_struct_0(sK1)
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_1001]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1006,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1)) | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1002,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1515,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,X0_70)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1006]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1571,plain,
% 2.36/0.99      ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,X0_70)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1573,plain,
% 2.36/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1571]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_10,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1023,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_775]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1024,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | v2_struct_0(sK1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_1023]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1028,plain,
% 2.36/0.99      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1024,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1029,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_1028]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1514,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1029]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1574,plain,
% 2.36/0.99      ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1576,plain,
% 2.36/0.99      ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 2.36/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1574]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1592,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.36/0.99      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.36/0.99      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.36/0.99      | sP0_iProver_split = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1521,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
% 2.36/0.99      | ~ sP0_iProver_split ),
% 2.36/0.99      inference(splitting,
% 2.36/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.36/0.99                [c_1508]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1593,plain,
% 2.36/0.99      ( k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | sP0_iProver_split != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1595,plain,
% 2.36/0.99      ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
% 2.36/0.99      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | sP0_iProver_split != iProver_top ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3831,plain,
% 2.36/0.99      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1818,c_46,c_1551,c_1560,c_1573,c_1576,c_1592,c_1595]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1519,negated_conjecture,
% 2.36/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1807,plain,
% 2.36/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_15,plain,
% 2.36/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_908,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X2)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
% 2.36/0.99      | sK2 != X2
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_909,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ l1_orders_2(sK1)
% 2.36/0.99      | v2_struct_0(sK2)
% 2.36/0.99      | v2_struct_0(sK1)
% 2.36/0.99      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_908]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_913,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_909,c_26,c_25,c_24,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1516,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_913]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1810,plain,
% 2.36/0.99      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1945,plain,
% 2.36/0.99      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1807,c_1810]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_14,plain,
% 2.36/0.99      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_5,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,X1)
% 2.36/0.99      | ~ l1_waybel_0(X0,X1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v8_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ l1_pre_topc(X1) ),
% 2.36/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_405,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,X1)
% 2.36/0.99      | ~ l1_waybel_0(X0,X1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.36/0.99      | ~ l1_waybel_9(X2)
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v8_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | X1 != X2 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_5]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_406,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,X1)
% 2.36/0.99      | ~ l1_waybel_0(X0,X1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.36/0.99      | ~ l1_waybel_9(X1)
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v8_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | v2_struct_0(X1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_405]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_726,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,X1)
% 2.36/0.99      | ~ l1_waybel_0(X0,X1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.36/0.99      | ~ l1_waybel_9(X1)
% 2.36/0.99      | ~ v2_pre_topc(X1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_406,c_31]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_727,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,sK1)
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.36/0.99      | ~ l1_waybel_9(sK1)
% 2.36/0.99      | ~ v2_pre_topc(sK1)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | v2_struct_0(sK1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_731,plain,
% 2.36/0.99      ( v2_struct_0(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | ~ v3_yellow_6(X0,sK1) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_727,c_32,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_732,plain,
% 2.36/0.99      ( ~ v3_yellow_6(X0,sK1)
% 2.36/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_731]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_847,plain,
% 2.36/0.99      ( ~ l1_waybel_0(X0,sK1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.36/0.99      | ~ v4_orders_2(X0)
% 2.36/0.99      | ~ v7_waybel_0(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | sK2 != X0
% 2.36/0.99      | sK1 != sK1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_732]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_848,plain,
% 2.36/0.99      ( ~ l1_waybel_0(sK2,sK1)
% 2.36/0.99      | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
% 2.36/0.99      | ~ v4_orders_2(sK2)
% 2.36/0.99      | ~ v7_waybel_0(sK2)
% 2.36/0.99      | v2_struct_0(sK2) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_847]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_850,plain,
% 2.36/0.99      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_848,c_24,c_23,c_22,c_20]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1517,plain,
% 2.36/0.99      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_850]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1809,plain,
% 2.36/0.99      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1517]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_6,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.36/0.99      | ~ l1_orders_2(X2)
% 2.36/0.99      | v2_struct_0(X2)
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.36/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1,plain,
% 2.36/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2,plain,
% 2.36/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.36/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_373,plain,
% 2.36/0.99      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.36/0.99      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_391,plain,
% 2.36/0.99      ( ~ l1_waybel_9(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.36/0.99      inference(resolution,[status(thm)],[c_14,c_373]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_763,plain,
% 2.36/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_391,c_25]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_764,plain,
% 2.36/0.99      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_763]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_56,plain,
% 2.36/0.99      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_92,plain,
% 2.36/0.99      ( v2_struct_0(sK1)
% 2.36/0.99      | ~ l1_struct_0(sK1)
% 2.36/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_95,plain,
% 2.36/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.36/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_766,plain,
% 2.36/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_764,c_26,c_25,c_56,c_59,c_89,c_92,c_95]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_785,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.36/0.99      | ~ l1_orders_2(X2)
% 2.36/0.99      | v2_struct_0(X2)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.36/0.99      | u1_struct_0(sK1) != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_766]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_786,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_785]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_947,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2)
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_786,c_775]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_948,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | v2_struct_0(sK1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_947]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_952,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_948,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_953,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_952]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1233,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(X2)
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,X2,X0) = k1_funct_1(X2,X0)
% 2.36/0.99      | k4_waybel_1(sK1,X1) != X2
% 2.36/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_935,c_953]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1234,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X1))
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_1233]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1248,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.36/0.99      inference(forward_subsumption_resolution,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1234,c_1006,c_1029]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1509,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.36/0.99      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1248]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1817,plain,
% 2.36/0.99      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
% 2.36/0.99      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3034,plain,
% 2.36/0.99      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1807,c_1817]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3141,plain,
% 2.36/0.99      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1809,c_3034]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_9,plain,
% 2.36/0.99      ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.36/0.99      | ~ l1_orders_2(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.36/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_190,plain,
% 2.36/0.99      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.36/0.99      | ~ l1_orders_2(X0)
% 2.36/0.99      | v2_struct_0(X0)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.36/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_11]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_191,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.36/0.99      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_190]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_974,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.36/0.99      | v2_struct_0(X1)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.36/0.99      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_191,c_775]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_975,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | v2_struct_0(sK1)
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_974]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_979,plain,
% 2.36/0.99      ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_975,c_26,c_25,c_59,c_89]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_980,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(renaming,[status(thm)],[c_979]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1018,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1006,c_980]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1040,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1029,c_1018]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1513,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1040]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1813,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2379,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k11_lattice3(sK1,sK3,X0_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1807,c_1813]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2397,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1809,c_2379]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_4,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.99      | ~ v5_orders_2(X1)
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | ~ v2_lattice3(X1)
% 2.36/0.99      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 2.36/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_643,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.36/0.99      | ~ l1_orders_2(X1)
% 2.36/0.99      | ~ v2_lattice3(X1)
% 2.36/0.99      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 2.36/0.99      | sK1 != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_28]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_644,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ l1_orders_2(sK1)
% 2.36/0.99      | ~ v2_lattice3(sK1)
% 2.36/0.99      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_643]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_648,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.36/0.99      inference(global_propositional_subsumption,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_644,c_26,c_25,c_59]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1518,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.36/0.99      | k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_648]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1808,plain,
% 2.36/0.99      ( k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1956,plain,
% 2.36/0.99      ( k11_lattice3(sK1,sK3,X0_70) = k12_lattice3(sK1,sK3,X0_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1807,c_1808]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2003,plain,
% 2.36/0.99      ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1809,c_1956]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2399,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_2397,c_2003]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_0,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | v1_xboole_0(X1)
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.36/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_812,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.36/0.99      | ~ m1_subset_1(X3,X1)
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.36/0.99      | u1_struct_0(sK1) != X1 ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_766]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_813,plain,
% 2.36/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
% 2.36/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
% 2.36/0.99      | ~ v1_funct_1(X0)
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_812]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1161,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X3)))
% 2.36/0.99      | ~ v1_funct_1(X2)
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),X3,X2,X0) = k1_funct_1(X2,X0)
% 2.36/0.99      | k4_waybel_1(sK1,X1) != X2
% 2.36/0.99      | u1_struct_0(sK1) != X3
% 2.36/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.36/0.99      inference(resolution_lifted,[status(thm)],[c_813,c_935]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1162,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.36/0.99      | ~ v1_funct_1(k4_waybel_1(sK1,X1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.36/0.99      inference(unflattening,[status(thm)],[c_1161]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1176,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.36/0.99      inference(forward_subsumption_resolution,
% 2.36/0.99                [status(thm)],
% 2.36/0.99                [c_1162,c_1006,c_1029]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1512,plain,
% 2.36/0.99      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.36/0.99      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.36/0.99      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_1176]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1814,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
% 2.36/0.99      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2450,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
% 2.36/0.99      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1807,c_1814]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2545,plain,
% 2.36/0.99      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(superposition,[status(thm)],[c_1809,c_2450]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_2627,plain,
% 2.36/0.99      ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(demodulation,[status(thm)],[c_2399,c_2545]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3143,plain,
% 2.36/0.99      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_3141,c_2627]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3835,plain,
% 2.36/0.99      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 2.36/0.99      inference(light_normalisation,[status(thm)],[c_3831,c_1945,c_3143]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_17,negated_conjecture,
% 2.36/0.99      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 2.36/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1520,negated_conjecture,
% 2.36/0.99      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 2.36/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_1806,plain,
% 2.36/0.99      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
% 2.36/0.99      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 2.36/0.99  
% 2.36/0.99  cnf(c_3837,plain,
% 2.36/0.99      ( $false ),
% 2.36/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3835,c_1806]) ).
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  ------                               Statistics
% 2.36/0.99  
% 2.36/0.99  ------ General
% 2.36/0.99  
% 2.36/0.99  abstr_ref_over_cycles:                  0
% 2.36/0.99  abstr_ref_under_cycles:                 0
% 2.36/0.99  gc_basic_clause_elim:                   0
% 2.36/0.99  forced_gc_time:                         0
% 2.36/0.99  parsing_time:                           0.01
% 2.36/0.99  unif_index_cands_time:                  0.
% 2.36/0.99  unif_index_add_time:                    0.
% 2.36/0.99  orderings_time:                         0.
% 2.36/0.99  out_proof_time:                         0.012
% 2.36/0.99  total_time:                             0.148
% 2.36/0.99  num_of_symbols:                         75
% 2.36/0.99  num_of_terms:                           2819
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing
% 2.36/0.99  
% 2.36/0.99  num_of_splits:                          1
% 2.36/0.99  num_of_split_atoms:                     1
% 2.36/0.99  num_of_reused_defs:                     0
% 2.36/0.99  num_eq_ax_congr_red:                    42
% 2.36/0.99  num_of_sem_filtered_clauses:            4
% 2.36/0.99  num_of_subtypes:                        8
% 2.36/0.99  monotx_restored_types:                  0
% 2.36/0.99  sat_num_of_epr_types:                   0
% 2.36/0.99  sat_num_of_non_cyclic_types:            0
% 2.36/0.99  sat_guarded_non_collapsed_types:        0
% 2.36/0.99  num_pure_diseq_elim:                    0
% 2.36/0.99  simp_replaced_by:                       0
% 2.36/0.99  res_preprocessed:                       112
% 2.36/0.99  prep_upred:                             0
% 2.36/0.99  prep_unflattend:                        28
% 2.36/0.99  smt_new_axioms:                         0
% 2.36/0.99  pred_elim_cands:                        3
% 2.36/0.99  pred_elim:                              18
% 2.36/0.99  pred_elim_cl:                           20
% 2.36/0.99  pred_elim_cycles:                       26
% 2.36/0.99  merged_defs:                            0
% 2.36/0.99  merged_defs_ncl:                        0
% 2.36/0.99  bin_hyper_res:                          0
% 2.36/0.99  prep_cycles:                            4
% 2.36/0.99  pred_elim_time:                         0.027
% 2.36/0.99  splitting_time:                         0.
% 2.36/0.99  sem_filter_time:                        0.
% 2.36/0.99  monotx_time:                            0.
% 2.36/0.99  subtype_inf_time:                       0.
% 2.36/0.99  
% 2.36/0.99  ------ Problem properties
% 2.36/0.99  
% 2.36/0.99  clauses:                                14
% 2.36/0.99  conjectures:                            2
% 2.36/0.99  epr:                                    0
% 2.36/0.99  horn:                                   12
% 2.36/0.99  ground:                                 4
% 2.36/0.99  unary:                                  3
% 2.36/0.99  binary:                                 3
% 2.36/0.99  lits:                                   36
% 2.36/0.99  lits_eq:                                9
% 2.36/0.99  fd_pure:                                0
% 2.36/0.99  fd_pseudo:                              0
% 2.36/0.99  fd_cond:                                0
% 2.36/0.99  fd_pseudo_cond:                         0
% 2.36/0.99  ac_symbols:                             0
% 2.36/0.99  
% 2.36/0.99  ------ Propositional Solver
% 2.36/0.99  
% 2.36/0.99  prop_solver_calls:                      30
% 2.36/0.99  prop_fast_solver_calls:                 979
% 2.36/0.99  smt_solver_calls:                       0
% 2.36/0.99  smt_fast_solver_calls:                  0
% 2.36/0.99  prop_num_of_clauses:                    934
% 2.36/0.99  prop_preprocess_simplified:             3705
% 2.36/0.99  prop_fo_subsumed:                       44
% 2.36/0.99  prop_solver_time:                       0.
% 2.36/0.99  smt_solver_time:                        0.
% 2.36/0.99  smt_fast_solver_time:                   0.
% 2.36/0.99  prop_fast_solver_time:                  0.
% 2.36/0.99  prop_unsat_core_time:                   0.
% 2.36/0.99  
% 2.36/0.99  ------ QBF
% 2.36/0.99  
% 2.36/0.99  qbf_q_res:                              0
% 2.36/0.99  qbf_num_tautologies:                    0
% 2.36/0.99  qbf_prep_cycles:                        0
% 2.36/0.99  
% 2.36/0.99  ------ BMC1
% 2.36/0.99  
% 2.36/0.99  bmc1_current_bound:                     -1
% 2.36/0.99  bmc1_last_solved_bound:                 -1
% 2.36/0.99  bmc1_unsat_core_size:                   -1
% 2.36/0.99  bmc1_unsat_core_parents_size:           -1
% 2.36/0.99  bmc1_merge_next_fun:                    0
% 2.36/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation
% 2.36/0.99  
% 2.36/0.99  inst_num_of_clauses:                    295
% 2.36/0.99  inst_num_in_passive:                    38
% 2.36/0.99  inst_num_in_active:                     223
% 2.36/0.99  inst_num_in_unprocessed:                34
% 2.36/0.99  inst_num_of_loops:                      240
% 2.36/0.99  inst_num_of_learning_restarts:          0
% 2.36/0.99  inst_num_moves_active_passive:          9
% 2.36/0.99  inst_lit_activity:                      0
% 2.36/0.99  inst_lit_activity_moves:                0
% 2.36/0.99  inst_num_tautologies:                   0
% 2.36/0.99  inst_num_prop_implied:                  0
% 2.36/0.99  inst_num_existing_simplified:           0
% 2.36/0.99  inst_num_eq_res_simplified:             0
% 2.36/0.99  inst_num_child_elim:                    0
% 2.36/0.99  inst_num_of_dismatching_blockings:      96
% 2.36/0.99  inst_num_of_non_proper_insts:           397
% 2.36/0.99  inst_num_of_duplicates:                 0
% 2.36/0.99  inst_inst_num_from_inst_to_res:         0
% 2.36/0.99  inst_dismatching_checking_time:         0.
% 2.36/0.99  
% 2.36/0.99  ------ Resolution
% 2.36/0.99  
% 2.36/0.99  res_num_of_clauses:                     0
% 2.36/0.99  res_num_in_passive:                     0
% 2.36/0.99  res_num_in_active:                      0
% 2.36/0.99  res_num_of_loops:                       116
% 2.36/0.99  res_forward_subset_subsumed:            129
% 2.36/0.99  res_backward_subset_subsumed:           2
% 2.36/0.99  res_forward_subsumed:                   0
% 2.36/0.99  res_backward_subsumed:                  0
% 2.36/0.99  res_forward_subsumption_resolution:     8
% 2.36/0.99  res_backward_subsumption_resolution:    2
% 2.36/0.99  res_clause_to_clause_subsumption:       171
% 2.36/0.99  res_orphan_elimination:                 0
% 2.36/0.99  res_tautology_del:                      82
% 2.36/0.99  res_num_eq_res_simplified:              1
% 2.36/0.99  res_num_sel_changes:                    0
% 2.36/0.99  res_moves_from_active_to_pass:          0
% 2.36/0.99  
% 2.36/0.99  ------ Superposition
% 2.36/0.99  
% 2.36/0.99  sup_time_total:                         0.
% 2.36/0.99  sup_time_generating:                    0.
% 2.36/0.99  sup_time_sim_full:                      0.
% 2.36/0.99  sup_time_sim_immed:                     0.
% 2.36/0.99  
% 2.36/0.99  sup_num_of_clauses:                     62
% 2.36/0.99  sup_num_in_active:                      45
% 2.36/0.99  sup_num_in_passive:                     17
% 2.36/0.99  sup_num_of_loops:                       47
% 2.36/0.99  sup_fw_superposition:                   37
% 2.36/0.99  sup_bw_superposition:                   14
% 2.36/0.99  sup_immediate_simplified:               10
% 2.36/0.99  sup_given_eliminated:                   0
% 2.36/0.99  comparisons_done:                       0
% 2.36/0.99  comparisons_avoided:                    9
% 2.36/0.99  
% 2.36/0.99  ------ Simplifications
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  sim_fw_subset_subsumed:                 0
% 2.36/0.99  sim_bw_subset_subsumed:                 0
% 2.36/0.99  sim_fw_subsumed:                        0
% 2.36/0.99  sim_bw_subsumed:                        0
% 2.36/0.99  sim_fw_subsumption_res:                 1
% 2.36/0.99  sim_bw_subsumption_res:                 0
% 2.36/0.99  sim_tautology_del:                      0
% 2.36/0.99  sim_eq_tautology_del:                   2
% 2.36/0.99  sim_eq_res_simp:                        0
% 2.36/0.99  sim_fw_demodulated:                     0
% 2.36/0.99  sim_bw_demodulated:                     2
% 2.36/0.99  sim_light_normalised:                   11
% 2.36/0.99  sim_joinable_taut:                      0
% 2.36/0.99  sim_joinable_simp:                      0
% 2.36/0.99  sim_ac_normalised:                      0
% 2.36/0.99  sim_smt_subsumption:                    0
% 2.36/0.99  
%------------------------------------------------------------------------------
