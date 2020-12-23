%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:53 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  228 (2194 expanded)
%              Number of clauses        :  150 ( 544 expanded)
%              Number of leaves         :   19 ( 677 expanded)
%              Depth                    :   25
%              Number of atoms          : 1088 (22535 expanded)
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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f45,f44,f43])).

fof(f76,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f24])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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

fof(f55,plain,(
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

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f80,plain,(
    ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( v3_yellow_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

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
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_565,plain,
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

cnf(c_566,plain,
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
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,negated_conjecture,
    ( v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_570,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26])).

cnf(c_571,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
    | ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_831,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_571])).

cnf(c_832,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23,negated_conjecture,
    ( v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_834,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_25,c_24,c_23,c_21])).

cnf(c_835,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
    inference(renaming,[status(thm)],[c_834])).

cnf(c_12,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_747,plain,
    ( l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_748,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_902,plain,
    ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_748])).

cnf(c_903,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_60,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_96,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_28,c_26,c_60,c_96])).

cnf(c_908,plain,
    ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_907])).

cnf(c_1111,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_835,c_908])).

cnf(c_1336,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_1111])).

cnf(c_1481,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_1336])).

cnf(c_1495,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
    | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1481])).

cnf(c_1791,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1511,plain,
    ( X0_70 != X1_70
    | k4_waybel_1(X0_69,X0_70) = k4_waybel_1(X0_69,X1_70) ),
    theory(equality)).

cnf(c_1524,plain,
    ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_1499,plain,
    ( X0_70 = X0_70 ),
    theory(equality)).

cnf(c_1533,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_974,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v1_funct_1(k4_waybel_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_748])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_28,c_26,c_60,c_96])).

cnf(c_1488,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | v1_funct_1(k4_waybel_1(sK1,X0_70)) ),
    inference(subtyping,[status(esa)],[c_979])).

cnf(c_1544,plain,
    ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,X0_70)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_1546,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_996,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_748])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_1001,plain,
    ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_28,c_26,c_60,c_96])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_1001])).

cnf(c_1487,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_1002])).

cnf(c_1547,plain,
    ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_1549,plain,
    ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_1565,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
    | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1481])).

cnf(c_1566,plain,
    ( k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_1568,plain,
    ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_3804,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_47,c_1524,c_1533,c_1546,c_1549,c_1565,c_1568])).

cnf(c_1492,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1780,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_881,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_882,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_882,c_28,c_26,c_25,c_60,c_96])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2) ),
    inference(subtyping,[status(esa)],[c_886])).

cnf(c_1783,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_1918,plain,
    ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1780,c_1783])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_448,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_6])).

cnf(c_449,plain,
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
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_697,plain,
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
    inference(resolution_lifted,[status(thm)],[c_449,c_32])).

cnf(c_698,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v3_yellow_6(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_33,c_28,c_26,c_60,c_96])).

cnf(c_703,plain,
    ( ~ v3_yellow_6(X0,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_702])).

cnf(c_820,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_703])).

cnf(c_821,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_823,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_25,c_24,c_23,c_21])).

cnf(c_1490,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_823])).

cnf(c_1782,plain,
    ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_398,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_420,plain,
    ( ~ l1_waybel_9(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_15,c_398])).

cnf(c_736,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_26])).

cnf(c_737,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_57,plain,
    ( ~ l1_waybel_9(sK1)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_90,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_99,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_739,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_28,c_26,c_57,c_60,c_90,c_96,c_99])).

cnf(c_758,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_739])).

cnf(c_759,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_920,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_759,c_748])).

cnf(c_921,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_28,c_26,c_60,c_96])).

cnf(c_926,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_925])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X2)
    | k2_yellow_6(u1_struct_0(sK1),sK1,X2,X0) = k1_funct_1(X2,X0)
    | k4_waybel_1(sK1,X1) != X2
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_908,c_926])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1206])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1207,c_979,c_1002])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
    inference(subtyping,[status(esa)],[c_1221])).

cnf(c_1790,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_3007,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1790])).

cnf(c_3114,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1782,c_3007])).

cnf(c_10,plain,
    ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(k4_waybel_1(X0,X1))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
    inference(cnf_transformation,[],[f81])).

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

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(k4_waybel_1(X1,X2))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_197,c_748])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_952,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_28,c_26,c_60,c_96])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_979,c_953])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1002,c_991])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70) ),
    inference(subtyping,[status(esa)],[c_1013])).

cnf(c_1786,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_2352,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k11_lattice3(sK1,sK3,X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1786])).

cnf(c_2370,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1782,c_2352])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_29,c_26,c_60])).

cnf(c_1491,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70) ),
    inference(subtyping,[status(esa)],[c_632])).

cnf(c_1781,plain,
    ( k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1929,plain,
    ( k11_lattice3(sK1,sK3,X0_70) = k12_lattice3(sK1,sK3,X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1781])).

cnf(c_1976,plain,
    ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1782,c_1929])).

cnf(c_2372,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2370,c_1976])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_785,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_739])).

cnf(c_786,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X3)))
    | ~ v1_funct_1(X2)
    | k3_funct_2(u1_struct_0(sK1),X3,X2,X0) = k1_funct_1(X2,X0)
    | k4_waybel_1(sK1,X1) != X2
    | u1_struct_0(sK1) != X3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_786,c_908])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_waybel_1(sK1,X1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1134])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1135,c_979,c_1002])).

cnf(c_1485,plain,
    ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
    inference(subtyping,[status(esa)],[c_1149])).

cnf(c_1787,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
    | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1485])).

cnf(c_2423,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
    | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1787])).

cnf(c_2518,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1782,c_2423])).

cnf(c_2600,plain,
    ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2372,c_2518])).

cnf(c_3116,plain,
    ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3114,c_2600])).

cnf(c_3808,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3804,c_1918,c_3116])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1493,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1779,plain,
    ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_3810,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3808,c_1779])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.47/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/1.00  
% 2.47/1.00  ------  iProver source info
% 2.47/1.00  
% 2.47/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.47/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/1.00  git: non_committed_changes: false
% 2.47/1.00  git: last_make_outside_of_git: false
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     num_symb
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       true
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  ------ Parsing...
% 2.47/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/1.00  ------ Proving...
% 2.47/1.00  ------ Problem Properties 
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  clauses                                 14
% 2.47/1.00  conjectures                             2
% 2.47/1.00  EPR                                     0
% 2.47/1.00  Horn                                    12
% 2.47/1.00  unary                                   3
% 2.47/1.00  binary                                  3
% 2.47/1.00  lits                                    36
% 2.47/1.00  lits eq                                 9
% 2.47/1.00  fd_pure                                 0
% 2.47/1.00  fd_pseudo                               0
% 2.47/1.00  fd_cond                                 0
% 2.47/1.00  fd_pseudo_cond                          0
% 2.47/1.00  AC symbols                              0
% 2.47/1.00  
% 2.47/1.00  ------ Schedule dynamic 5 is on 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  Current options:
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     none
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       false
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ Proving...
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  % SZS status Theorem for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00   Resolution empty clause
% 2.47/1.00  
% 2.47/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  fof(f13,conjecture,(
% 2.47/1.00    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f14,negated_conjecture,(
% 2.47/1.00    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 2.47/1.00    inference(negated_conjecture,[],[f13])).
% 2.47/1.00  
% 2.47/1.00  fof(f36,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f14])).
% 2.47/1.00  
% 2.47/1.00  fof(f37,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f36])).
% 2.47/1.00  
% 2.47/1.00  fof(f45,plain,(
% 2.47/1.00    ( ! [X0,X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_hidden(k12_lattice3(X0,sK3,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,sK3,X1))) & v5_pre_topc(k4_waybel_1(X0,sK3),X0,X0) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f44,plain,(
% 2.47/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,sK2)),k10_yellow_6(X0,k3_waybel_2(X0,X2,sK2))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2,X0) & v3_yellow_6(sK2,X0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f43,plain,(
% 2.47/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK1,X2,k11_yellow_6(sK1,X1)),k10_yellow_6(sK1,k3_waybel_2(sK1,X2,X1))) & v5_pre_topc(k4_waybel_1(sK1,X2),sK1,sK1) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(X1,sK1) & v3_yellow_6(X1,sK1) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f46,plain,(
% 2.47/1.00    ((~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) & v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) & m1_subset_1(sK3,u1_struct_0(sK1))) & l1_waybel_0(sK2,sK1) & v3_yellow_6(sK2,sK1) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_waybel_9(sK1) & v2_lattice3(sK1) & v1_lattice3(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & v8_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f45,f44,f43])).
% 2.47/1.00  
% 2.47/1.00  fof(f76,plain,(
% 2.47/1.00    v3_yellow_6(sK2,sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f12,axiom,(
% 2.47/1.00    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f34,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f12])).
% 2.47/1.00  
% 2.47/1.00  fof(f35,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.47/1.00    inference(flattening,[],[f34])).
% 2.47/1.00  
% 2.47/1.00  fof(f64,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f35])).
% 2.47/1.00  
% 2.47/1.00  fof(f79,plain,(
% 2.47/1.00    v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f65,plain,(
% 2.47/1.00    v2_pre_topc(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f66,plain,(
% 2.47/1.00    v8_pre_topc(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f67,plain,(
% 2.47/1.00    v3_orders_2(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f68,plain,(
% 2.47/1.00    v4_orders_2(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f69,plain,(
% 2.47/1.00    v5_orders_2(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f70,plain,(
% 2.47/1.00    v1_lattice3(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f71,plain,(
% 2.47/1.00    v2_lattice3(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f72,plain,(
% 2.47/1.00    l1_waybel_9(sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f73,plain,(
% 2.47/1.00    ~v2_struct_0(sK2)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f74,plain,(
% 2.47/1.00    v4_orders_2(sK2)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f75,plain,(
% 2.47/1.00    v7_waybel_0(sK2)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f77,plain,(
% 2.47/1.00    l1_waybel_0(sK2,sK1)),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f9,axiom,(
% 2.47/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f29,plain,(
% 2.47/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f9])).
% 2.47/1.00  
% 2.47/1.00  fof(f30,plain,(
% 2.47/1.00    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(flattening,[],[f29])).
% 2.47/1.00  
% 2.47/1.00  fof(f59,plain,(
% 2.47/1.00    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f10,axiom,(
% 2.47/1.00    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f31,plain,(
% 2.47/1.00    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f10])).
% 2.47/1.00  
% 2.47/1.00  fof(f62,plain,(
% 2.47/1.00    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f31])).
% 2.47/1.00  
% 2.47/1.00  fof(f3,axiom,(
% 2.47/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f18,plain,(
% 2.47/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f3])).
% 2.47/1.00  
% 2.47/1.00  fof(f19,plain,(
% 2.47/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.47/1.00    inference(flattening,[],[f18])).
% 2.47/1.00  
% 2.47/1.00  fof(f49,plain,(
% 2.47/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f19])).
% 2.47/1.00  
% 2.47/1.00  fof(f78,plain,(
% 2.47/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  fof(f58,plain,(
% 2.47/1.00    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f60,plain,(
% 2.47/1.00    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f11,axiom,(
% 2.47/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f32,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f11])).
% 2.47/1.00  
% 2.47/1.00  fof(f33,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(flattening,[],[f32])).
% 2.47/1.00  
% 2.47/1.00  fof(f63,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f33])).
% 2.47/1.00  
% 2.47/1.00  fof(f61,plain,(
% 2.47/1.00    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f31])).
% 2.47/1.00  
% 2.47/1.00  fof(f6,axiom,(
% 2.47/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f23,plain,(
% 2.47/1.00    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f6])).
% 2.47/1.00  
% 2.47/1.00  fof(f24,plain,(
% 2.47/1.00    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(flattening,[],[f23])).
% 2.47/1.00  
% 2.47/1.00  fof(f53,plain,(
% 2.47/1.00    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f24])).
% 2.47/1.00  
% 2.47/1.00  fof(f7,axiom,(
% 2.47/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f25,plain,(
% 2.47/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f7])).
% 2.47/1.00  
% 2.47/1.00  fof(f26,plain,(
% 2.47/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 2.47/1.00    inference(flattening,[],[f25])).
% 2.47/1.00  
% 2.47/1.00  fof(f54,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f26])).
% 2.47/1.00  
% 2.47/1.00  fof(f2,axiom,(
% 2.47/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f17,plain,(
% 2.47/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f2])).
% 2.47/1.00  
% 2.47/1.00  fof(f48,plain,(
% 2.47/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f17])).
% 2.47/1.00  
% 2.47/1.00  fof(f5,axiom,(
% 2.47/1.00    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f22,plain,(
% 2.47/1.00    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.47/1.00    inference(ennf_transformation,[],[f5])).
% 2.47/1.00  
% 2.47/1.00  fof(f38,plain,(
% 2.47/1.00    ! [X0] : (((v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) & (v1_xboole_0(u1_struct_0(X0)) | ~v2_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.47/1.00    inference(nnf_transformation,[],[f22])).
% 2.47/1.00  
% 2.47/1.00  fof(f52,plain,(
% 2.47/1.00    ( ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f38])).
% 2.47/1.00  
% 2.47/1.00  fof(f8,axiom,(
% 2.47/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f27,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f8])).
% 2.47/1.00  
% 2.47/1.00  fof(f28,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(flattening,[],[f27])).
% 2.47/1.00  
% 2.47/1.00  fof(f39,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(nnf_transformation,[],[f28])).
% 2.47/1.00  
% 2.47/1.00  fof(f40,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(rectify,[],[f39])).
% 2.47/1.00  
% 2.47/1.00  fof(f41,plain,(
% 2.47/1.00    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f42,plain,(
% 2.47/1.00    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK0(X0,X1,X2)) != k11_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.47/1.00  
% 2.47/1.00  fof(f55,plain,(
% 2.47/1.00    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f42])).
% 2.47/1.00  
% 2.47/1.00  fof(f81,plain,(
% 2.47/1.00    ( ! [X4,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.47/1.00    inference(equality_resolution,[],[f55])).
% 2.47/1.00  
% 2.47/1.00  fof(f4,axiom,(
% 2.47/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f20,plain,(
% 2.47/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f4])).
% 2.47/1.00  
% 2.47/1.00  fof(f21,plain,(
% 2.47/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.47/1.00    inference(flattening,[],[f20])).
% 2.47/1.00  
% 2.47/1.00  fof(f50,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f21])).
% 2.47/1.00  
% 2.47/1.00  fof(f1,axiom,(
% 2.47/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f15,plain,(
% 2.47/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f1])).
% 2.47/1.00  
% 2.47/1.00  fof(f16,plain,(
% 2.47/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.47/1.00    inference(flattening,[],[f15])).
% 2.47/1.00  
% 2.47/1.00  fof(f47,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f16])).
% 2.47/1.00  
% 2.47/1.00  fof(f80,plain,(
% 2.47/1.00    ~r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2)))),
% 2.47/1.00    inference(cnf_transformation,[],[f46])).
% 2.47/1.00  
% 2.47/1.00  cnf(c_22,negated_conjecture,
% 2.47/1.00      ( v3_yellow_6(sK2,sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_17,plain,
% 2.47/1.00      ( ~ v5_pre_topc(X0,X1,X1)
% 2.47/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.47/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.47/1.00      | ~ v3_yellow_6(X2,X1)
% 2.47/1.00      | ~ l1_waybel_0(X2,X1)
% 2.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.00      | ~ v3_orders_2(X1)
% 2.47/1.00      | ~ l1_waybel_9(X1)
% 2.47/1.00      | ~ v2_pre_topc(X1)
% 2.47/1.00      | ~ v8_pre_topc(X1)
% 2.47/1.00      | ~ v4_orders_2(X2)
% 2.47/1.00      | ~ v4_orders_2(X1)
% 2.47/1.00      | ~ v7_waybel_0(X2)
% 2.47/1.00      | ~ v5_orders_2(X1)
% 2.47/1.00      | ~ v2_lattice3(X1)
% 2.47/1.00      | ~ v1_lattice3(X1)
% 2.47/1.00      | v2_struct_0(X2)
% 2.47/1.00      | ~ v1_funct_1(X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_19,negated_conjecture,
% 2.47/1.00      ( v5_pre_topc(k4_waybel_1(sK1,sK3),sK1,sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_565,plain,
% 2.47/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X1))
% 2.47/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X0,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X0,X2)))
% 2.47/1.00      | ~ v3_yellow_6(X2,X1)
% 2.47/1.00      | ~ l1_waybel_0(X2,X1)
% 2.47/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.00      | ~ v3_orders_2(X1)
% 2.47/1.00      | ~ l1_waybel_9(X1)
% 2.47/1.00      | ~ v2_pre_topc(X1)
% 2.47/1.00      | ~ v8_pre_topc(X1)
% 2.47/1.00      | ~ v4_orders_2(X1)
% 2.47/1.00      | ~ v4_orders_2(X2)
% 2.47/1.00      | ~ v7_waybel_0(X2)
% 2.47/1.00      | ~ v5_orders_2(X1)
% 2.47/1.00      | ~ v2_lattice3(X1)
% 2.47/1.00      | ~ v1_lattice3(X1)
% 2.47/1.00      | v2_struct_0(X2)
% 2.47/1.00      | ~ v1_funct_1(X0)
% 2.47/1.00      | k4_waybel_1(sK1,sK3) != X0
% 2.47/1.00      | sK1 != X1 ),
% 2.47/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_566,plain,
% 2.47/1.00      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.47/1.00      | ~ v3_yellow_6(X0,sK1)
% 2.47/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.00      | ~ v3_orders_2(sK1)
% 2.47/1.00      | ~ l1_waybel_9(sK1)
% 2.47/1.00      | ~ v2_pre_topc(sK1)
% 2.47/1.00      | ~ v8_pre_topc(sK1)
% 2.47/1.00      | ~ v4_orders_2(X0)
% 2.47/1.00      | ~ v4_orders_2(sK1)
% 2.47/1.00      | ~ v7_waybel_0(X0)
% 2.47/1.00      | ~ v5_orders_2(sK1)
% 2.47/1.00      | ~ v2_lattice3(sK1)
% 2.47/1.00      | ~ v1_lattice3(sK1)
% 2.47/1.00      | v2_struct_0(X0)
% 2.47/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_33,negated_conjecture,
% 2.47/1.00      ( v2_pre_topc(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_32,negated_conjecture,
% 2.47/1.00      ( v8_pre_topc(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_31,negated_conjecture,
% 2.47/1.00      ( v3_orders_2(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_30,negated_conjecture,
% 2.47/1.00      ( v4_orders_2(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_29,negated_conjecture,
% 2.47/1.00      ( v5_orders_2(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_28,negated_conjecture,
% 2.47/1.00      ( v1_lattice3(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_27,negated_conjecture,
% 2.47/1.00      ( v2_lattice3(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_26,negated_conjecture,
% 2.47/1.00      ( l1_waybel_9(sK1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_570,plain,
% 2.47/1.00      ( ~ v7_waybel_0(X0)
% 2.47/1.00      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.00      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.47/1.00      | ~ v3_yellow_6(X0,sK1)
% 2.47/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.00      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.00      | ~ v4_orders_2(X0)
% 2.47/1.00      | v2_struct_0(X0)
% 2.47/1.00      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_566,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_571,plain,
% 2.47/1.01      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.47/1.01      | ~ v3_yellow_6(X0,sK1)
% 2.47/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_570]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_831,plain,
% 2.47/1.01      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,X0)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),X0)))
% 2.47/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.47/1.01      | sK2 != X0
% 2.47/1.01      | sK1 != sK1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_571]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_832,plain,
% 2.47/1.01      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ l1_waybel_0(sK2,sK1)
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v4_orders_2(sK2)
% 2.47/1.01      | ~ v7_waybel_0(sK2)
% 2.47/1.01      | v2_struct_0(sK2)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_831]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_25,negated_conjecture,
% 2.47/1.01      ( ~ v2_struct_0(sK2) ),
% 2.47/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_24,negated_conjecture,
% 2.47/1.01      ( v4_orders_2(sK2) ),
% 2.47/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_23,negated_conjecture,
% 2.47/1.01      ( v7_waybel_0(sK2) ),
% 2.47/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_21,negated_conjecture,
% 2.47/1.01      ( l1_waybel_0(sK2,sK1) ),
% 2.47/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_834,plain,
% 2.47/1.01      ( ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_832,c_25,c_24,c_23,c_21]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_835,plain,
% 2.47/1.01      ( ~ v1_funct_2(k4_waybel_1(sK1,sK3),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3)) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_834]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_12,plain,
% 2.47/1.01      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.47/1.01      | ~ l1_orders_2(X0)
% 2.47/1.01      | v2_struct_0(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_14,plain,
% 2.47/1.01      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_747,plain,
% 2.47/1.01      ( l1_orders_2(X0) | sK1 != X0 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_748,plain,
% 2.47/1.01      ( l1_orders_2(sK1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_747]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_902,plain,
% 2.47/1.01      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | sK1 != X0 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_748]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_903,plain,
% 2.47/1.01      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | v2_struct_0(sK1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_902]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_60,plain,
% 2.47/1.01      ( ~ l1_waybel_9(sK1) | l1_orders_2(sK1) ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2,plain,
% 2.47/1.01      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_96,plain,
% 2.47/1.01      ( ~ l1_orders_2(sK1) | ~ v1_lattice3(sK1) | ~ v2_struct_0(sK1) ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_907,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_903,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_908,plain,
% 2.47/1.01      ( v1_funct_2(k4_waybel_1(sK1,X0),u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_907]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1111,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.47/1.01      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3)
% 2.47/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_835,c_908]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1336,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.47/1.01      | k4_waybel_1(sK1,X0) != k4_waybel_1(sK1,sK3) ),
% 2.47/1.01      inference(equality_resolution_simp,[status(thm)],[c_1111]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1481,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.47/1.01      | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_1336]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1495,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2)))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,sK3))
% 2.47/1.01      | sP0_iProver_split ),
% 2.47/1.01      inference(splitting,
% 2.47/1.01                [splitting(split),new_symbols(definition,[])],
% 2.47/1.01                [c_1481]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1791,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.47/1.01      | sP0_iProver_split = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_20,negated_conjecture,
% 2.47/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.47/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_47,plain,
% 2.47/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1511,plain,
% 2.47/1.01      ( X0_70 != X1_70 | k4_waybel_1(X0_69,X0_70) = k4_waybel_1(X0_69,X1_70) ),
% 2.47/1.01      theory(equality) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1524,plain,
% 2.47/1.01      ( k4_waybel_1(sK1,sK3) = k4_waybel_1(sK1,sK3) | sK3 != sK3 ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1511]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1499,plain,( X0_70 = X0_70 ),theory(equality) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1533,plain,
% 2.47/1.01      ( sK3 = sK3 ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1499]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_13,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | v1_funct_1(k4_waybel_1(X1,X0)) ),
% 2.47/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_974,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | v1_funct_1(k4_waybel_1(X1,X0))
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_748]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_975,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | v2_struct_0(sK1)
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_974]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_979,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1)) | v1_funct_1(k4_waybel_1(sK1,X0)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_975,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1488,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,X0_70)) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_979]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1544,plain,
% 2.47/1.01      ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,X0_70)) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1546,plain,
% 2.47/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,sK3)) = iProver_top ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_11,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X1) ),
% 2.47/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_996,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | m1_subset_1(k4_waybel_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_748]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_997,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | v2_struct_0(sK1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_996]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1001,plain,
% 2.47/1.01      ( m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_997,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1002,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_1001]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1487,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_1002]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1547,plain,
% 2.47/1.01      ( m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,X0_70),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1549,plain,
% 2.47/1.01      ( m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
% 2.47/1.01      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1547]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1565,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top
% 2.47/1.01      | m1_subset_1(k4_waybel_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top
% 2.47/1.01      | v1_funct_1(k4_waybel_1(sK1,sK3)) != iProver_top
% 2.47/1.01      | sP0_iProver_split = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1494,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
% 2.47/1.01      | ~ sP0_iProver_split ),
% 2.47/1.01      inference(splitting,
% 2.47/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.47/1.01                [c_1481]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1566,plain,
% 2.47/1.01      ( k4_waybel_1(sK1,X0_70) != k4_waybel_1(sK1,sK3)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | sP0_iProver_split != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1568,plain,
% 2.47/1.01      ( k4_waybel_1(sK1,sK3) != k4_waybel_1(sK1,sK3)
% 2.47/1.01      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | sP0_iProver_split != iProver_top ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1566]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3804,plain,
% 2.47/1.01      ( r2_hidden(k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2))) = iProver_top ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_1791,c_47,c_1524,c_1533,c_1546,c_1549,c_1565,c_1568]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1492,negated_conjecture,
% 2.47/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1780,plain,
% 2.47/1.01      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_16,plain,
% 2.47/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X2),X0) = k3_waybel_2(X1,X2,X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_881,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X2)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | k6_waybel_9(X1,X1,k4_waybel_1(X1,X0),X2) = k3_waybel_2(X1,X0,X2)
% 2.47/1.01      | sK2 != X2
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_882,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ l1_orders_2(sK1)
% 2.47/1.01      | v2_struct_0(sK2)
% 2.47/1.01      | v2_struct_0(sK1)
% 2.47/1.01      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_881]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_886,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0),sK2) = k3_waybel_2(sK1,X0,sK2) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_882,c_28,c_26,c_25,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1489,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_886]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1783,plain,
% 2.47/1.01      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,X0_70),sK2) = k3_waybel_2(sK1,X0_70,sK2)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1918,plain,
% 2.47/1.01      ( k6_waybel_9(sK1,sK1,k4_waybel_1(sK1,sK3),sK2) = k3_waybel_2(sK1,sK3,sK2) ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1780,c_1783]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_15,plain,
% 2.47/1.01      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_6,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.47/1.01      | ~ l1_waybel_0(X0,X1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.47/1.01      | ~ v2_pre_topc(X1)
% 2.47/1.01      | ~ v8_pre_topc(X1)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | ~ l1_pre_topc(X1) ),
% 2.47/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_448,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.47/1.01      | ~ l1_waybel_0(X0,X1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.47/1.01      | ~ l1_waybel_9(X2)
% 2.47/1.01      | ~ v2_pre_topc(X1)
% 2.47/1.01      | ~ v8_pre_topc(X1)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | X1 != X2 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_6]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_449,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.47/1.01      | ~ l1_waybel_0(X0,X1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.47/1.01      | ~ l1_waybel_9(X1)
% 2.47/1.01      | ~ v2_pre_topc(X1)
% 2.47/1.01      | ~ v8_pre_topc(X1)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | v2_struct_0(X1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_448]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_697,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,X1)
% 2.47/1.01      | ~ l1_waybel_0(X0,X1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(X1,X0),u1_struct_0(X1))
% 2.47/1.01      | ~ l1_waybel_9(X1)
% 2.47/1.01      | ~ v2_pre_topc(X1)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_449,c_32]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_698,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,sK1)
% 2.47/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.47/1.01      | ~ l1_waybel_9(sK1)
% 2.47/1.01      | ~ v2_pre_topc(sK1)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | v2_struct_0(sK1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_697]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_702,plain,
% 2.47/1.01      ( v2_struct_0(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.47/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | ~ v3_yellow_6(X0,sK1) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_698,c_33,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_703,plain,
% 2.47/1.01      ( ~ v3_yellow_6(X0,sK1)
% 2.47/1.01      | ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_702]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_820,plain,
% 2.47/1.01      ( ~ l1_waybel_0(X0,sK1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(sK1,X0),u1_struct_0(sK1))
% 2.47/1.01      | ~ v4_orders_2(X0)
% 2.47/1.01      | ~ v7_waybel_0(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | sK2 != X0
% 2.47/1.01      | sK1 != sK1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_703]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_821,plain,
% 2.47/1.01      ( ~ l1_waybel_0(sK2,sK1)
% 2.47/1.01      | m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1))
% 2.47/1.01      | ~ v4_orders_2(sK2)
% 2.47/1.01      | ~ v7_waybel_0(sK2)
% 2.47/1.01      | v2_struct_0(sK2) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_820]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_823,plain,
% 2.47/1.01      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_821,c_25,c_24,c_23,c_21]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1490,plain,
% 2.47/1.01      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_823]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1782,plain,
% 2.47/1.01      ( m1_subset_1(k11_yellow_6(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_7,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.47/1.01      | ~ m1_subset_1(X3,X1)
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.47/1.01      | ~ l1_orders_2(X2)
% 2.47/1.01      | v2_struct_0(X2)
% 2.47/1.01      | v1_xboole_0(X1)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.47/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1,plain,
% 2.47/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_4,plain,
% 2.47/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.47/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_398,plain,
% 2.47/1.01      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.47/1.01      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_420,plain,
% 2.47/1.01      ( ~ l1_waybel_9(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.47/1.01      inference(resolution,[status(thm)],[c_15,c_398]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_736,plain,
% 2.47/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_420,c_26]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_737,plain,
% 2.47/1.01      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_736]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_57,plain,
% 2.47/1.01      ( ~ l1_waybel_9(sK1) | l1_pre_topc(sK1) ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_90,plain,
% 2.47/1.01      ( v2_struct_0(sK1)
% 2.47/1.01      | ~ l1_struct_0(sK1)
% 2.47/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_99,plain,
% 2.47/1.01      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.47/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_739,plain,
% 2.47/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_737,c_28,c_26,c_57,c_60,c_90,c_96,c_99]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_758,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(X2))
% 2.47/1.01      | ~ m1_subset_1(X3,X1)
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
% 2.47/1.01      | ~ l1_orders_2(X2)
% 2.47/1.01      | v2_struct_0(X2)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.47/1.01      | u1_struct_0(sK1) != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_739]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_759,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_758]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_920,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2)
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_759,c_748]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_921,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | v2_struct_0(sK1)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_920]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_925,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_921,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_926,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,X0,X1) = k1_funct_1(X0,X1) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_925]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1206,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(X2)
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,X2,X0) = k1_funct_1(X2,X0)
% 2.47/1.01      | k4_waybel_1(sK1,X1) != X2
% 2.47/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_908,c_926]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1207,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,X1))
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_1206]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1221,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.47/1.01      inference(forward_subsumption_resolution,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_1207,c_979,c_1002]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1482,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.47/1.01      | k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_1221]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1790,plain,
% 2.47/1.01      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
% 2.47/1.01      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3007,plain,
% 2.47/1.01      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1780,c_1790]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3114,plain,
% 2.47/1.01      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1782,c_3007]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_10,plain,
% 2.47/1.01      ( ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.47/1.01      | ~ l1_orders_2(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.47/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_196,plain,
% 2.47/1.01      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 2.47/1.01      | ~ l1_orders_2(X0)
% 2.47/1.01      | v2_struct_0(X0)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(X0,X1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X2) = k11_lattice3(X0,X1,X2) ),
% 2.47/1.01      inference(global_propositional_subsumption,[status(thm)],[c_10,c_12]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_197,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.47/1.01      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_196]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_947,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
% 2.47/1.01      | v2_struct_0(X1)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(X1,X2))
% 2.47/1.01      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) = k11_lattice3(X1,X2,X0)
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_197,c_748]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_948,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | v2_struct_0(sK1)
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_947]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_952,plain,
% 2.47/1.01      ( ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_948,c_28,c_26,c_60,c_96]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_953,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,X0))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(renaming,[status(thm)],[c_952]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_991,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_979,c_953]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1013,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0),X1) = k11_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1002,c_991]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1486,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_1013]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1786,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k11_lattice3(sK1,X0_70,X1_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2352,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k11_lattice3(sK1,sK3,X0_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1780,c_1786]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2370,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1782,c_2352]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.47/1.01      | ~ v5_orders_2(X1)
% 2.47/1.01      | ~ v2_lattice3(X1)
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 2.47/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_627,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.47/1.01      | ~ v5_orders_2(X1)
% 2.47/1.01      | ~ l1_orders_2(X1)
% 2.47/1.01      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 2.47/1.01      | sK1 != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_628,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ v5_orders_2(sK1)
% 2.47/1.01      | ~ l1_orders_2(sK1)
% 2.47/1.01      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_627]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_632,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | k11_lattice3(sK1,X0,X1) = k12_lattice3(sK1,X0,X1) ),
% 2.47/1.01      inference(global_propositional_subsumption,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_628,c_29,c_26,c_60]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1491,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.47/1.01      | k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_632]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1781,plain,
% 2.47/1.01      ( k11_lattice3(sK1,X0_70,X1_70) = k12_lattice3(sK1,X0_70,X1_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1929,plain,
% 2.47/1.01      ( k11_lattice3(sK1,sK3,X0_70) = k12_lattice3(sK1,sK3,X0_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1780,c_1781]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1976,plain,
% 2.47/1.01      ( k11_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1782,c_1929]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2372,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_2370,c_1976]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_0,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.47/1.01      | ~ m1_subset_1(X3,X1)
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/1.01      | v1_xboole_0(X1)
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.47/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_785,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.47/1.01      | ~ m1_subset_1(X3,X1)
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
% 2.47/1.01      | u1_struct_0(sK1) != X1 ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_739]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_786,plain,
% 2.47/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
% 2.47/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
% 2.47/1.01      | ~ v1_funct_1(X0)
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_785]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1134,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X3)))
% 2.47/1.01      | ~ v1_funct_1(X2)
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),X3,X2,X0) = k1_funct_1(X2,X0)
% 2.47/1.01      | k4_waybel_1(sK1,X1) != X2
% 2.47/1.01      | u1_struct_0(sK1) != X3
% 2.47/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.47/1.01      inference(resolution_lifted,[status(thm)],[c_786,c_908]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1135,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(k4_waybel_1(sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 2.47/1.01      | ~ v1_funct_1(k4_waybel_1(sK1,X1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.47/1.01      inference(unflattening,[status(thm)],[c_1134]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1149,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1),X0) = k1_funct_1(k4_waybel_1(sK1,X1),X0) ),
% 2.47/1.01      inference(forward_subsumption_resolution,
% 2.47/1.01                [status(thm)],
% 2.47/1.01                [c_1135,c_979,c_1002]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1485,plain,
% 2.47/1.01      ( ~ m1_subset_1(X0_70,u1_struct_0(sK1))
% 2.47/1.01      | ~ m1_subset_1(X1_70,u1_struct_0(sK1))
% 2.47/1.01      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X1_70),X0_70) = k1_funct_1(k4_waybel_1(sK1,X1_70),X0_70) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_1149]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1787,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,X0_70),X1_70) = k1_funct_1(k4_waybel_1(sK1,X0_70),X1_70)
% 2.47/1.01      | m1_subset_1(X1_70,u1_struct_0(sK1)) != iProver_top
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1485]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2423,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),X0_70) = k1_funct_1(k4_waybel_1(sK1,sK3),X0_70)
% 2.47/1.01      | m1_subset_1(X0_70,u1_struct_0(sK1)) != iProver_top ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1780,c_1787]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2518,plain,
% 2.47/1.01      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(superposition,[status(thm)],[c_1782,c_2423]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_2600,plain,
% 2.47/1.01      ( k1_funct_1(k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(demodulation,[status(thm)],[c_2372,c_2518]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3116,plain,
% 2.47/1.01      ( k2_yellow_6(u1_struct_0(sK1),sK1,k4_waybel_1(sK1,sK3),k11_yellow_6(sK1,sK2)) = k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)) ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_3114,c_2600]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3808,plain,
% 2.47/1.01      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) = iProver_top ),
% 2.47/1.01      inference(light_normalisation,[status(thm)],[c_3804,c_1918,c_3116]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_18,negated_conjecture,
% 2.47/1.01      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 2.47/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1493,negated_conjecture,
% 2.47/1.01      ( ~ r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) ),
% 2.47/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_1779,plain,
% 2.47/1.01      ( r2_hidden(k12_lattice3(sK1,sK3,k11_yellow_6(sK1,sK2)),k10_yellow_6(sK1,k3_waybel_2(sK1,sK3,sK2))) != iProver_top ),
% 2.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1493]) ).
% 2.47/1.01  
% 2.47/1.01  cnf(c_3810,plain,
% 2.47/1.01      ( $false ),
% 2.47/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3808,c_1779]) ).
% 2.47/1.01  
% 2.47/1.01  
% 2.47/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/1.01  
% 2.47/1.01  ------                               Statistics
% 2.47/1.01  
% 2.47/1.01  ------ General
% 2.47/1.01  
% 2.47/1.01  abstr_ref_over_cycles:                  0
% 2.47/1.01  abstr_ref_under_cycles:                 0
% 2.47/1.01  gc_basic_clause_elim:                   0
% 2.47/1.01  forced_gc_time:                         0
% 2.47/1.01  parsing_time:                           0.012
% 2.47/1.01  unif_index_cands_time:                  0.
% 2.47/1.01  unif_index_add_time:                    0.
% 2.47/1.01  orderings_time:                         0.
% 2.47/1.01  out_proof_time:                         0.02
% 2.47/1.01  total_time:                             0.177
% 2.47/1.01  num_of_symbols:                         75
% 2.47/1.01  num_of_terms:                           2691
% 2.47/1.01  
% 2.47/1.01  ------ Preprocessing
% 2.47/1.01  
% 2.47/1.01  num_of_splits:                          1
% 2.47/1.01  num_of_split_atoms:                     1
% 2.47/1.01  num_of_reused_defs:                     0
% 2.47/1.01  num_eq_ax_congr_red:                    42
% 2.47/1.01  num_of_sem_filtered_clauses:            4
% 2.47/1.01  num_of_subtypes:                        8
% 2.47/1.01  monotx_restored_types:                  0
% 2.47/1.01  sat_num_of_epr_types:                   0
% 2.47/1.01  sat_num_of_non_cyclic_types:            0
% 2.47/1.01  sat_guarded_non_collapsed_types:        0
% 2.47/1.01  num_pure_diseq_elim:                    0
% 2.47/1.01  simp_replaced_by:                       0
% 2.47/1.01  res_preprocessed:                       113
% 2.47/1.01  prep_upred:                             0
% 2.47/1.01  prep_unflattend:                        27
% 2.47/1.01  smt_new_axioms:                         0
% 2.47/1.01  pred_elim_cands:                        3
% 2.47/1.01  pred_elim:                              18
% 2.47/1.01  pred_elim_cl:                           21
% 2.47/1.01  pred_elim_cycles:                       25
% 2.47/1.01  merged_defs:                            0
% 2.47/1.01  merged_defs_ncl:                        0
% 2.47/1.01  bin_hyper_res:                          0
% 2.47/1.01  prep_cycles:                            4
% 2.47/1.01  pred_elim_time:                         0.044
% 2.47/1.01  splitting_time:                         0.
% 2.47/1.01  sem_filter_time:                        0.
% 2.47/1.01  monotx_time:                            0.
% 2.47/1.01  subtype_inf_time:                       0.
% 2.47/1.01  
% 2.47/1.01  ------ Problem properties
% 2.47/1.01  
% 2.47/1.01  clauses:                                14
% 2.47/1.01  conjectures:                            2
% 2.47/1.01  epr:                                    0
% 2.47/1.01  horn:                                   12
% 2.47/1.01  ground:                                 4
% 2.47/1.01  unary:                                  3
% 2.47/1.01  binary:                                 3
% 2.47/1.01  lits:                                   36
% 2.47/1.01  lits_eq:                                9
% 2.47/1.01  fd_pure:                                0
% 2.47/1.01  fd_pseudo:                              0
% 2.47/1.01  fd_cond:                                0
% 2.47/1.01  fd_pseudo_cond:                         0
% 2.47/1.01  ac_symbols:                             0
% 2.47/1.01  
% 2.47/1.01  ------ Propositional Solver
% 2.47/1.01  
% 2.47/1.01  prop_solver_calls:                      30
% 2.47/1.01  prop_fast_solver_calls:                 975
% 2.47/1.01  smt_solver_calls:                       0
% 2.47/1.01  smt_fast_solver_calls:                  0
% 2.47/1.01  prop_num_of_clauses:                    938
% 2.47/1.01  prop_preprocess_simplified:             3741
% 2.47/1.01  prop_fo_subsumed:                       44
% 2.47/1.01  prop_solver_time:                       0.
% 2.47/1.01  smt_solver_time:                        0.
% 2.47/1.01  smt_fast_solver_time:                   0.
% 2.47/1.01  prop_fast_solver_time:                  0.
% 2.47/1.01  prop_unsat_core_time:                   0.
% 2.47/1.01  
% 2.47/1.01  ------ QBF
% 2.47/1.01  
% 2.47/1.01  qbf_q_res:                              0
% 2.47/1.01  qbf_num_tautologies:                    0
% 2.47/1.01  qbf_prep_cycles:                        0
% 2.47/1.01  
% 2.47/1.01  ------ BMC1
% 2.47/1.01  
% 2.47/1.01  bmc1_current_bound:                     -1
% 2.47/1.01  bmc1_last_solved_bound:                 -1
% 2.47/1.01  bmc1_unsat_core_size:                   -1
% 2.47/1.01  bmc1_unsat_core_parents_size:           -1
% 2.47/1.01  bmc1_merge_next_fun:                    0
% 2.47/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.47/1.01  
% 2.47/1.01  ------ Instantiation
% 2.47/1.01  
% 2.47/1.01  inst_num_of_clauses:                    295
% 2.47/1.01  inst_num_in_passive:                    38
% 2.47/1.01  inst_num_in_active:                     223
% 2.47/1.01  inst_num_in_unprocessed:                34
% 2.47/1.01  inst_num_of_loops:                      240
% 2.47/1.01  inst_num_of_learning_restarts:          0
% 2.47/1.01  inst_num_moves_active_passive:          9
% 2.47/1.01  inst_lit_activity:                      0
% 2.47/1.01  inst_lit_activity_moves:                0
% 2.47/1.01  inst_num_tautologies:                   0
% 2.47/1.01  inst_num_prop_implied:                  0
% 2.47/1.01  inst_num_existing_simplified:           0
% 2.47/1.01  inst_num_eq_res_simplified:             0
% 2.47/1.01  inst_num_child_elim:                    0
% 2.47/1.01  inst_num_of_dismatching_blockings:      96
% 2.47/1.01  inst_num_of_non_proper_insts:           397
% 2.47/1.01  inst_num_of_duplicates:                 0
% 2.47/1.01  inst_inst_num_from_inst_to_res:         0
% 2.47/1.01  inst_dismatching_checking_time:         0.
% 2.47/1.01  
% 2.47/1.01  ------ Resolution
% 2.47/1.01  
% 2.47/1.01  res_num_of_clauses:                     0
% 2.47/1.01  res_num_in_passive:                     0
% 2.47/1.01  res_num_in_active:                      0
% 2.47/1.01  res_num_of_loops:                       117
% 2.47/1.01  res_forward_subset_subsumed:            130
% 2.47/1.01  res_backward_subset_subsumed:           2
% 2.47/1.01  res_forward_subsumed:                   0
% 2.47/1.01  res_backward_subsumed:                  0
% 2.47/1.01  res_forward_subsumption_resolution:     8
% 2.47/1.01  res_backward_subsumption_resolution:    2
% 2.47/1.01  res_clause_to_clause_subsumption:       170
% 2.47/1.01  res_orphan_elimination:                 0
% 2.47/1.01  res_tautology_del:                      82
% 2.47/1.01  res_num_eq_res_simplified:              1
% 2.47/1.01  res_num_sel_changes:                    0
% 2.47/1.01  res_moves_from_active_to_pass:          0
% 2.47/1.01  
% 2.47/1.01  ------ Superposition
% 2.47/1.01  
% 2.47/1.01  sup_time_total:                         0.
% 2.47/1.01  sup_time_generating:                    0.
% 2.47/1.01  sup_time_sim_full:                      0.
% 2.47/1.01  sup_time_sim_immed:                     0.
% 2.47/1.01  
% 2.47/1.01  sup_num_of_clauses:                     62
% 2.47/1.01  sup_num_in_active:                      45
% 2.47/1.01  sup_num_in_passive:                     17
% 2.47/1.01  sup_num_of_loops:                       47
% 2.47/1.01  sup_fw_superposition:                   37
% 2.47/1.01  sup_bw_superposition:                   14
% 2.47/1.01  sup_immediate_simplified:               10
% 2.47/1.01  sup_given_eliminated:                   0
% 2.47/1.01  comparisons_done:                       0
% 2.47/1.01  comparisons_avoided:                    9
% 2.47/1.01  
% 2.47/1.01  ------ Simplifications
% 2.47/1.01  
% 2.47/1.01  
% 2.47/1.01  sim_fw_subset_subsumed:                 0
% 2.47/1.01  sim_bw_subset_subsumed:                 0
% 2.47/1.01  sim_fw_subsumed:                        0
% 2.47/1.01  sim_bw_subsumed:                        0
% 2.47/1.01  sim_fw_subsumption_res:                 1
% 2.47/1.01  sim_bw_subsumption_res:                 0
% 2.47/1.01  sim_tautology_del:                      0
% 2.47/1.01  sim_eq_tautology_del:                   2
% 2.47/1.01  sim_eq_res_simp:                        0
% 2.47/1.01  sim_fw_demodulated:                     0
% 2.47/1.01  sim_bw_demodulated:                     2
% 2.47/1.01  sim_light_normalised:                   11
% 2.47/1.01  sim_joinable_taut:                      0
% 2.47/1.01  sim_joinable_simp:                      0
% 2.47/1.01  sim_ac_normalised:                      0
% 2.47/1.01  sim_smt_subsumption:                    0
% 2.47/1.01  
%------------------------------------------------------------------------------
