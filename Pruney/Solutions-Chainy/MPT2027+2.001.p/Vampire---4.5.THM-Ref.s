%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  161 (1582 expanded)
%              Number of leaves         :   17 ( 565 expanded)
%              Depth                    :   33
%              Number of atoms          :  876 (18098 expanded)
%              Number of equality atoms :   63 (  63 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f821,plain,(
    $false ),
    inference(subsumption_resolution,[],[f820,f62])).

fof(f62,plain,(
    ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v3_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_waybel_9(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f40,f39,f38])).

fof(f38,plain,
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
              ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v3_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1)))
            & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(X1,sK0)
        & v3_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1)))
          & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_0(sK1,sK0)
      & v3_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1)))
        & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
      & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_9)).

fof(f820,plain,(
    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(backward_demodulation,[],[f600,f818])).

fof(f818,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f814,f742])).

fof(f742,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f738,f328])).

fof(f328,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f244,f183])).

fof(f183,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3) ) ),
    inference(subsumption_resolution,[],[f182,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f182,plain,(
    ! [X3] :
      ( k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f53])).

fof(f53,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f181,plain,(
    ! [X3] :
      ( k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f107])).

fof(f107,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f54,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f54,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f169,plain,(
    ! [X3] :
      ( k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f60,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f244,plain,(
    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f243,f107])).

fof(f243,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f241,f52])).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f241,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f141,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f140,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f48])).

fof(f48,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f106])).

fof(f106,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f138,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f137,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f56,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f136,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f57])).

fof(f57,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f135,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f59,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f58,plain,(
    v3_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f738,plain,(
    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f315,f244])).

fof(f315,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f190,f217])).

fof(f217,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f52])).

fof(f207,plain,
    ( ~ v2_struct_0(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(resolution,[],[f107,f68])).

fof(f190,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) ) ),
    inference(subsumption_resolution,[],[f189,f178])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f166,f107])).

fof(f166,plain,
    ( v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f189,plain,(
    ! [X5] :
      ( k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f188,f179])).

fof(f179,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f167,f107])).

fof(f167,plain,
    ( v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f188,plain,(
    ! [X5] :
      ( k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f180])).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f168,f107])).

fof(f168,plain,
    ( m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f187,plain,(
    ! [X5] :
      ( k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f107])).

fof(f171,plain,(
    ! [X5] :
      ( k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2))
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_1)).

fof(f814,plain,(
    k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f464,f244])).

fof(f464,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5) ) ),
    inference(subsumption_resolution,[],[f463,f240])).

fof(f240,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f239,f217])).

fof(f239,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f160,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(f160,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f463,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f462,f237])).

fof(f237,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f236,f107])).

fof(f236,plain,
    ( v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f234,f52])).

fof(f234,plain,
    ( v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f178,f68])).

fof(f462,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f435,f271])).

fof(f271,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f180,f217])).

fof(f435,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f249,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f249,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f248,f107])).

fof(f248,plain,
    ( v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f246,f52])).

fof(f246,plain,
    ( v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f179,f68])).

fof(f600,plain,(
    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(subsumption_resolution,[],[f599,f240])).

fof(f599,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f598,f217])).

fof(f598,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f597,f107])).

fof(f597,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f596,f237])).

fof(f596,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f595,f249])).

fof(f595,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f594,f271])).

fof(f594,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f587,f244])).

fof(f587,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f422,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(f422,plain,(
    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(forward_demodulation,[],[f421,f312])).

fof(f312,plain,(
    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f311,f217])).

fof(f311,plain,
    ( k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f310,f55])).

fof(f310,plain,
    ( k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f177,f59])).

fof(f177,plain,(
    ! [X2] :
      ( ~ l1_waybel_0(X2,sK0)
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X2) = k3_waybel_2(sK0,sK2,X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f107])).

fof(f165,plain,(
    ! [X2] :
      ( k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X2) = k3_waybel_2(sK0,sK2,X2)
      | ~ l1_waybel_0(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_9)).

fof(f421,plain,(
    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f420,f237])).

fof(f420,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f419,f249])).

fof(f419,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f418,f271])).

fof(f418,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(resolution,[],[f153,f61])).

fof(f61,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f152,f47])).

fof(f152,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f48])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f50])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f149,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f147,f52])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f53])).

fof(f146,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_waybel_9(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_9(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_waybel_9(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f57])).

fof(f142,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_waybel_9(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_waybel_9(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_9)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (29621)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.43  % (29621)Refutation not found, incomplete strategy% (29621)------------------------------
% 0.22/0.43  % (29621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29621)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (29621)Memory used [KB]: 1791
% 0.22/0.43  % (29621)Time elapsed: 0.007 s
% 0.22/0.43  % (29621)------------------------------
% 0.22/0.43  % (29621)------------------------------
% 0.22/0.46  % (29612)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (29624)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (29612)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f821,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f820,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ((~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) & m1_subset_1(sK2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v3_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f40,f39,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v3_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v3_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v3_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_9)).
% 0.22/0.50  fof(f820,plain,(
% 0.22/0.50    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.50    inference(backward_demodulation,[],[f600,f818])).
% 0.22/0.50  fof(f818,plain,(
% 0.22/0.50    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.50    inference(forward_demodulation,[],[f814,f742])).
% 0.22/0.50  fof(f742,plain,(
% 0.22/0.50    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.50    inference(forward_demodulation,[],[f738,f328])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1))),
% 0.22/0.50    inference(resolution,[],[f244,f183])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f182,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X3] : (k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v5_orders_2(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f181,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v2_lattice3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ( ! [X3] : (k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(resolution,[],[f54,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    l1_waybel_9(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X3] : (k12_lattice3(sK0,sK2,X3) = k11_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f60,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f243,f107])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f241,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_lattice3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(resolution,[],[f141,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f140,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v8_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f138,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(resolution,[],[f54,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f137,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v4_orders_2(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f135,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v7_waybel_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f133,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    l1_waybel_0(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f58,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v3_yellow_6(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f738,plain,(
% 0.22/0.50    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.50    inference(resolution,[],[f315,f244])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.50    inference(resolution,[],[f190,f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f207,f52])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | ~v1_lattice3(sK0)),
% 0.22/0.50    inference(resolution,[],[f107,f68])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X5] : (v2_struct_0(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f189,f178])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f166,f107])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f60,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X5] : (k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f188,f179])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f167,f107])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f60,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ( ! [X5] : (k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f187,f180])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.50    inference(subsumption_resolution,[],[f168,f107])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f60,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ( ! [X5] : (k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f171,f107])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X5] : (k11_lattice3(sK0,sK2,X5) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f60,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_1)).
% 0.22/0.50  fof(f814,plain,(
% 0.22/0.50    k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.50    inference(resolution,[],[f464,f244])).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f463,f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f239,f217])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f160,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0] : (((v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) & (v1_xboole_0(u1_struct_0(X0)) | ~v2_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f106,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    ( ! [X5] : (k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f462,f237])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f236,f107])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f234,f52])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(resolution,[],[f178,f68])).
% 0.22/0.50  fof(f462,plain,(
% 0.22/0.50    ( ! [X5] : (k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f435,f271])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.50    inference(resolution,[],[f180,f217])).
% 0.22/0.50  fof(f435,plain,(
% 0.22/0.50    ( ! [X5] : (k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X5) = k1_funct_1(k4_waybel_1(sK0,sK2),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f249,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f248,f107])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f246,f52])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.50    inference(resolution,[],[f179,f68])).
% 0.22/0.50  fof(f600,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f599,f240])).
% 0.22/0.50  fof(f599,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f598,f217])).
% 0.22/0.50  fof(f598,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f597,f107])).
% 0.22/0.50  fof(f597,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f596,f237])).
% 0.22/0.50  fof(f596,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f595,f249])).
% 0.22/0.50  fof(f595,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f594,f271])).
% 0.22/0.50  fof(f594,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f587,f244])).
% 0.22/0.50  fof(f587,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(superposition,[],[f422,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).
% 0.22/0.50  fof(f422,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.50    inference(forward_demodulation,[],[f421,f312])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f311,f217])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f310,f55])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f177,f59])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ( ! [X2] : (~l1_waybel_0(X2,sK0) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X2) = k3_waybel_2(sK0,sK2,X2) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f165,f107])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ( ! [X2] : (k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X2) = k3_waybel_2(sK0,sK2,X2) | ~l1_waybel_0(X2,sK0) | v2_struct_0(X2) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f60,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_9)).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f420,f237])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f419,f249])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f418,f271])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.50    inference(resolution,[],[f153,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f152,f47])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f151,f48])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f150,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f149,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f148,f51])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f147,f52])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f146,f53])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f145,f54])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f144,f55])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f143,f56])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f142,f57])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f134,f59])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f58,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_9)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (29612)------------------------------
% 0.22/0.50  % (29612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29612)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (29612)Memory used [KB]: 2174
% 0.22/0.50  % (29612)Time elapsed: 0.081 s
% 0.22/0.50  % (29612)------------------------------
% 0.22/0.50  % (29612)------------------------------
% 0.22/0.50  % (29600)Success in time 0.138 s
%------------------------------------------------------------------------------
