%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  200 (2860 expanded)
%              Number of leaves         :   19 (1044 expanded)
%              Depth                    :   45
%              Number of atoms          : 1649 (44316 expanded)
%              Number of equality atoms :   78 (2740 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(subsumption_resolution,[],[f448,f71])).

fof(f71,plain,(
    sK1 != k1_waybel_2(sK0,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK1 != k1_waybel_2(sK0,sK2)
    & r3_waybel_9(sK0,sK2,sK1)
    & v10_waybel_0(sK2,sK0)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_2(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v10_waybel_0(X2,X0)
                & ! [X3] :
                    ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(sK0,X2) != X1
              & r3_waybel_9(sK0,X2,X1)
              & v10_waybel_0(X2,sK0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_waybel_2(sK0,X2) != X1
            & r3_waybel_9(sK0,X2,X1)
            & v10_waybel_0(X2,sK0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_waybel_2(sK0,X2) != sK1
          & r3_waybel_9(sK0,X2,sK1)
          & v10_waybel_0(X2,sK0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k1_waybel_2(sK0,X2) != sK1
        & r3_waybel_9(sK0,X2,sK1)
        & v10_waybel_0(X2,sK0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( sK1 != k1_waybel_2(sK0,sK2)
      & r3_waybel_9(sK0,sK2,sK1)
      & v10_waybel_0(sK2,sK0)
      & ! [X3] :
          ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
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
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r3_waybel_9(X0,X2,X1)
                    & v10_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).

fof(f448,plain,(
    sK1 = k1_waybel_2(sK0,sK2) ),
    inference(backward_demodulation,[],[f144,f444])).

fof(f444,plain,(
    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f58,f111,f63,f261,f436,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
        & r2_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f436,plain,(
    ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f435,f71])).

fof(f435,plain,
    ( sK1 = k1_waybel_2(sK0,sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f434,f144])).

fof(f434,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f433,f261])).

fof(f433,plain,
    ( sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f432,f70])).

fof(f70,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f432,plain,
    ( ~ r3_waybel_9(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f430,f63])).

fof(f430,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_waybel_9(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f425,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r3_orders_2(sK0,sK1,sK5(sK0,sK1,X0))
      | sK1 = k1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X0,sK1)
      | ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f225,f160])).

fof(f160,plain,(
    ! [X6] :
      ( r1_orders_2(sK0,sK1,X6)
      | ~ r3_orders_2(sK0,sK1,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f136,f63])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X1,X0)
      | r1_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f135,f126])).

fof(f126,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f60,f111,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f60,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X1,X0)
      | r1_orders_2(sK0,X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f111])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X0,X1)
      | r1_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f56,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f225,plain,(
    ! [X6] :
      ( ~ r1_orders_2(sK0,sK1,sK5(sK0,sK1,X6))
      | ~ r2_lattice3(sK0,X6,sK1)
      | sK1 = k1_yellow_0(sK0,X6) ) ),
    inference(resolution,[],[f183,f63])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,sK5(sK0,X1,X0))
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f107,f111])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ l1_orders_2(sK0)
      | ~ r2_lattice3(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X3))
      | k1_yellow_0(sK0,X3) = X2 ) ),
    inference(resolution,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f425,plain,(
    ! [X0] :
      ( r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f424,f71])).

fof(f424,plain,(
    ! [X0] :
      ( sK1 = k1_waybel_2(sK0,sK2)
      | ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ) ),
    inference(forward_demodulation,[],[f423,f144])).

fof(f423,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ) ),
    inference(subsumption_resolution,[],[f422,f58])).

fof(f422,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f421,f111])).

fof(f421,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f420,f63])).

fof(f420,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f418,f261])).

fof(f418,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
      | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
      | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f291,f83])).

fof(f291,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r3_orders_2(sK0,X4,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ) ),
    inference(resolution,[],[f281,f267])).

fof(f267,plain,(
    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f266,f71])).

fof(f266,plain,
    ( sK1 = k1_waybel_2(sK0,sK2)
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f265,f144])).

fof(f265,plain,
    ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f264,f63])).

fof(f264,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f262,f70])).

fof(f262,plain,
    ( ~ r3_waybel_9(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))
    | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(resolution,[],[f260,f206])).

fof(f206,plain,(
    ! [X6] :
      ( ~ r2_lattice3(sK0,X6,sK1)
      | r2_lattice3(sK0,X6,sK5(sK0,sK1,X6))
      | sK1 = k1_yellow_0(sK0,X6) ) ),
    inference(resolution,[],[f173,f63])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f106,f111])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ r2_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,sK5(sK0,X1,X0))
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f260,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ r3_waybel_9(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f259,f202])).

fof(f202,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f201,f137])).

fof(f137,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f131,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f131,plain,(
    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f67,f125,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f125,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f111,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f67,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f200,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f55])).

fof(f55,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f56])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f57])).

fof(f57,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f58])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f59])).

fof(f59,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f60])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f61])).

fof(f61,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f62,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f67])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f122,f69])).

fof(f69,plain,(
    v10_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f122,plain,(
    ! [X6,X7] :
      ( ~ v10_waybel_0(sK2,X6)
      | ~ r3_waybel_9(X6,sK2,X7)
      | m1_subset_1(sK3(X6),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_waybel_0(sK2,X6)
      | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7)
      | ~ l1_waybel_9(X6)
      | ~ v1_compts_1(X6)
      | ~ v2_lattice3(X6)
      | ~ v1_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | ~ v8_pre_topc(X6)
      | ~ v2_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f121,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f121,plain,(
    ! [X6,X7] :
      ( ~ r3_waybel_9(X6,sK2,X7)
      | ~ v10_waybel_0(sK2,X6)
      | m1_subset_1(sK3(X6),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_waybel_0(sK2,X6)
      | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X6)
      | ~ v1_compts_1(X6)
      | ~ v2_lattice3(X6)
      | ~ v1_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | ~ v8_pre_topc(X6)
      | ~ v2_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f115,f65])).

fof(f65,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,(
    ! [X6,X7] :
      ( ~ r3_waybel_9(X6,sK2,X7)
      | ~ v10_waybel_0(sK2,X6)
      | m1_subset_1(sK3(X6),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_waybel_0(sK2,X6)
      | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X6)
      | ~ v1_compts_1(X6)
      | ~ v2_lattice3(X6)
      | ~ v1_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | ~ v8_pre_topc(X6)
      | ~ v2_pre_topc(X6) ) ),
    inference(resolution,[],[f66,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
                    & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).

fof(f66,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f259,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f222,f68])).

fof(f68,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f222,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ r3_waybel_9(sK0,sK2,X0)
      | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f221,f137])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f220,f54])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f55])).

fof(f219,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f56])).

fof(f218,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f57])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f59])).

fof(f215,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f214,f60])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f213,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f212,f62])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f211,f67])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK2,X0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2,sK0)
      | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f124,f69])).

fof(f124,plain,(
    ! [X8,X9] :
      ( ~ v10_waybel_0(sK2,X8)
      | ~ r3_waybel_9(X8,sK2,X9)
      | ~ v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_waybel_0(sK2,X8)
      | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9)
      | ~ l1_waybel_9(X8)
      | ~ v1_compts_1(X8)
      | ~ v2_lattice3(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | ~ v4_orders_2(X8)
      | ~ v3_orders_2(X8)
      | ~ v8_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f123,f64])).

fof(f123,plain,(
    ! [X8,X9] :
      ( ~ r3_waybel_9(X8,sK2,X9)
      | ~ v10_waybel_0(sK2,X8)
      | ~ v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_waybel_0(sK2,X8)
      | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X8)
      | ~ v1_compts_1(X8)
      | ~ v2_lattice3(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | ~ v4_orders_2(X8)
      | ~ v3_orders_2(X8)
      | ~ v8_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f116,f65])).

fof(f116,plain,(
    ! [X8,X9] :
      ( ~ r3_waybel_9(X8,sK2,X9)
      | ~ v10_waybel_0(sK2,X8)
      | ~ v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_waybel_0(sK2,X8)
      | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X8)
      | ~ v1_compts_1(X8)
      | ~ v2_lattice3(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | ~ v4_orders_2(X8)
      | ~ v3_orders_2(X8)
      | ~ v8_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(resolution,[],[f66,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f280,f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X0) ) ),
    inference(forward_demodulation,[],[f239,f137])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f238,f54])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f55])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f56])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f57])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f59])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f60])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f61])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f62])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f118,f67])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK2,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
      | r3_orders_2(X0,X2,X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f117,f64])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK2,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(sK2,X0)
      | r3_orders_2(X0,X2,X1)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f113,f65])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,sK2,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(sK2,X0)
      | r3_orders_2(X0,X2,X1)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f66,f103])).

fof(f103,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_orders_2(X0,X3,X4)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
                    & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f258,f68])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X1,X0) ) ),
    inference(forward_demodulation,[],[f257,f137])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f256,f54])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f55])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f56])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f57])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f58])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f251,f59])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f60])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f249,f61])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f62])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK2,X1)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
      | r3_orders_2(sK0,X1,X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f120,f67])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_waybel_0(sK2,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r3_waybel_9(X3,sK2,X5)
      | ~ v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)
      | r3_orders_2(X3,X5,X4)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f119,f64])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r3_waybel_9(X3,sK2,X5)
      | ~ v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(sK2,X3)
      | r3_orders_2(X3,X5,X4)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f114,f65])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r3_waybel_9(X3,sK2,X5)
      | ~ v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(sK2,X3)
      | r3_orders_2(X3,X5,X4)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f66,f102])).

fof(f102,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_orders_2(X0,X3,X4)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f261,plain,(
    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f63,f70,f260])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    l1_orders_2(sK0) ),
    inference(unit_resulting_resolution,[],[f62,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f58,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f144,plain,(
    k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f142,f132])).

fof(f132,plain,(
    k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f111,f67,f126,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_waybel_0(X1,X0)
      | k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).

fof(f142,plain,(
    k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f126,f111,f138,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_relat_1(X1)
      | k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).

fof(f138,plain,(
    v1_relat_1(u1_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f131,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (31275)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.45  % (31275)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f449,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f448,f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    sK1 != k1_waybel_2(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ((sK1 != k1_waybel_2(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v10_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f44,f43,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (k1_waybel_2(sK0,X2) != X1 & r3_waybel_9(sK0,X2,X1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_waybel_2(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ? [X2] : (k1_waybel_2(sK0,X2) != sK1 & r3_waybel_9(sK0,X2,sK1) & v10_waybel_0(X2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (sK1 != k1_waybel_2(sK0,sK2) & r3_waybel_9(sK0,sK2,sK1) & v10_waybel_0(sK2,sK0) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).
% 0.21/0.45  fof(f448,plain,(
% 0.21/0.45    sK1 = k1_waybel_2(sK0,sK2)),
% 0.21/0.45    inference(backward_demodulation,[],[f144,f444])).
% 0.21/0.45  fof(f444,plain,(
% 0.21/0.45    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f58,f111,f63,f261,f436,f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK5(X0,X1,X2)) & r2_lattice3(X0,X2,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.45    inference(rectify,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.45  fof(f436,plain,(
% 0.21/0.45    ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f435,f71])).
% 0.21/0.45  fof(f435,plain,(
% 0.21/0.45    sK1 = k1_waybel_2(sK0,sK2) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.45    inference(forward_demodulation,[],[f434,f144])).
% 0.21/0.45  fof(f434,plain,(
% 0.21/0.45    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f433,f261])).
% 0.21/0.45  fof(f433,plain,(
% 0.21/0.45    sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.45    inference(subsumption_resolution,[],[f432,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f432,plain,(
% 0.21/0.46    ~r3_waybel_9(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f430,f63])).
% 0.21/0.46  fof(f430,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f425,f241])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_orders_2(sK0,sK1,sK5(sK0,sK1,X0)) | sK1 = k1_yellow_0(sK0,X0) | ~r2_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f225,f160])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    ( ! [X6] : (r1_orders_2(sK0,sK1,X6) | ~r3_orders_2(sK0,sK1,X6) | ~m1_subset_1(X6,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f136,f63])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X1,X0) | r1_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f135,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f60,f111,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    v2_lattice3(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X1,X0) | r1_orders_2(sK0,X1,X0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f104,f111])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f56,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    v3_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    ( ! [X6] : (~r1_orders_2(sK0,sK1,sK5(sK0,sK1,X6)) | ~r2_lattice3(sK0,X6,sK1) | sK1 = k1_yellow_0(sK0,X6)) )),
% 0.21/0.46    inference(resolution,[],[f183,f63])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X1,sK5(sK0,X1,X0)) | k1_yellow_0(sK0,X0) = X1) )),
% 0.21/0.46    inference(resolution,[],[f107,f111])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ( ! [X2,X3] : (~l1_orders_2(sK0) | ~r2_lattice3(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X3)) | k1_yellow_0(sK0,X3) = X2) )),
% 0.21/0.46    inference(resolution,[],[f58,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f52])).
% 0.21/0.46  fof(f425,plain,(
% 0.21/0.46    ( ! [X0] : (r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f424,f71])).
% 0.21/0.46  fof(f424,plain,(
% 0.21/0.46    ( ! [X0] : (sK1 = k1_waybel_2(sK0,sK2) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f423,f144])).
% 0.21/0.46  fof(f423,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f422,f58])).
% 0.21/0.46  fof(f422,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~v5_orders_2(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f421,f111])).
% 0.21/0.46  fof(f421,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f420,f63])).
% 0.21/0.46  fof(f420,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f418,f261])).
% 0.21/0.46  fof(f418,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f291,f83])).
% 0.21/0.46  fof(f291,plain,(
% 0.21/0.46    ( ! [X4] : (~m1_subset_1(sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r3_orders_2(sK0,X4,sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))) )),
% 0.21/0.46    inference(resolution,[],[f281,f267])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.46    inference(subsumption_resolution,[],[f266,f71])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    sK1 = k1_waybel_2(sK0,sK2) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2))))),
% 0.21/0.46    inference(forward_demodulation,[],[f265,f144])).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f264,f63])).
% 0.21/0.46  fof(f264,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f262,f70])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ~r3_waybel_9(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relat_1(u1_waybel_0(sK0,sK2)))) | sK1 = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.46    inference(resolution,[],[f260,f206])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ( ! [X6] : (~r2_lattice3(sK0,X6,sK1) | r2_lattice3(sK0,X6,sK5(sK0,sK1,X6)) | sK1 = k1_yellow_0(sK0,X6)) )),
% 0.21/0.46    inference(resolution,[],[f173,f63])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r2_lattice3(sK0,X0,sK5(sK0,X1,X0)) | k1_yellow_0(sK0,X0) = X1) )),
% 0.21/0.46    inference(resolution,[],[f106,f111])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,sK5(sK0,X1,X0)) | k1_yellow_0(sK0,X0) = X1) )),
% 0.21/0.46    inference(resolution,[],[f58,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | r2_lattice3(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f52])).
% 0.21/0.46  fof(f260,plain,(
% 0.21/0.46    ( ! [X0] : (r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f259,f202])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    ( ! [X0] : (r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f201,f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = k2_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f131,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f67,f125,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    l1_struct_0(sK0)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f111,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    l1_waybel_0(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f200,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f199,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v8_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f198,f56])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f197,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    v4_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f196,f58])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f195,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    v1_lattice3(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f194,f60])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f193,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    v1_compts_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f192,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    l1_waybel_9(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f191,f67])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f122,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    v10_waybel_0(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X6,X7] : (~v10_waybel_0(sK2,X6) | ~r3_waybel_9(X6,sK2,X7) | m1_subset_1(sK3(X6),u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_waybel_0(sK2,X6) | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7) | ~l1_waybel_9(X6) | ~v1_compts_1(X6) | ~v2_lattice3(X6) | ~v1_lattice3(X6) | ~v5_orders_2(X6) | ~v4_orders_2(X6) | ~v3_orders_2(X6) | ~v8_pre_topc(X6) | ~v2_pre_topc(X6)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f121,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ~v2_struct_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X6,X7] : (~r3_waybel_9(X6,sK2,X7) | ~v10_waybel_0(sK2,X6) | m1_subset_1(sK3(X6),u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_waybel_0(sK2,X6) | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7) | v2_struct_0(sK2) | ~l1_waybel_9(X6) | ~v1_compts_1(X6) | ~v2_lattice3(X6) | ~v1_lattice3(X6) | ~v5_orders_2(X6) | ~v4_orders_2(X6) | ~v3_orders_2(X6) | ~v8_pre_topc(X6) | ~v2_pre_topc(X6)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f115,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    v4_orders_2(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X6,X7] : (~r3_waybel_9(X6,sK2,X7) | ~v10_waybel_0(sK2,X6) | m1_subset_1(sK3(X6),u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_waybel_0(sK2,X6) | r2_lattice3(X6,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X6),u1_waybel_0(X6,sK2)),X7) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X6) | ~v1_compts_1(X6) | ~v2_lattice3(X6) | ~v1_lattice3(X6) | ~v5_orders_2(X6) | ~v4_orders_2(X6) | ~v3_orders_2(X6) | ~v8_pre_topc(X6) | ~v2_pre_topc(X6)) )),
% 0.21/0.46    inference(resolution,[],[f66,f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    v7_waybel_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f222,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ( ! [X0] : (~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f221,f137])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f220,f54])).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f219,f55])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f218,f56])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f217,f57])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f216,f58])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f215,f59])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f214,f60])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f213,f61])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f212,f62])).
% 0.21/0.46  fof(f212,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f211,f67])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK2,sK0) | r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f124,f69])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X8,X9] : (~v10_waybel_0(sK2,X8) | ~r3_waybel_9(X8,sK2,X9) | ~v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_waybel_0(sK2,X8) | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9) | ~l1_waybel_9(X8) | ~v1_compts_1(X8) | ~v2_lattice3(X8) | ~v1_lattice3(X8) | ~v5_orders_2(X8) | ~v4_orders_2(X8) | ~v3_orders_2(X8) | ~v8_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f123,f64])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ( ! [X8,X9] : (~r3_waybel_9(X8,sK2,X9) | ~v10_waybel_0(sK2,X8) | ~v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_waybel_0(sK2,X8) | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9) | v2_struct_0(sK2) | ~l1_waybel_9(X8) | ~v1_compts_1(X8) | ~v2_lattice3(X8) | ~v1_lattice3(X8) | ~v5_orders_2(X8) | ~v4_orders_2(X8) | ~v3_orders_2(X8) | ~v8_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f116,f65])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X8,X9] : (~r3_waybel_9(X8,sK2,X9) | ~v10_waybel_0(sK2,X8) | ~v5_pre_topc(k4_waybel_1(X8,sK3(X8)),X8,X8) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_waybel_0(sK2,X8) | r2_lattice3(X8,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X8),u1_waybel_0(X8,sK2)),X9) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X8) | ~v1_compts_1(X8) | ~v2_lattice3(X8) | ~v1_lattice3(X8) | ~v5_orders_2(X8) | ~v4_orders_2(X8) | ~v3_orders_2(X8) | ~v8_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 0.21/0.46    inference(resolution,[],[f66,f100])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f280,f240])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f239,f137])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f238,f54])).
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f237,f55])).
% 0.21/0.46  fof(f237,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f236,f56])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f235,f57])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f234,f58])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f233,f59])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f232,f60])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f231,f61])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f230,f62])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f118,f67])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK2,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | r3_orders_2(X0,X2,X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f117,f64])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK2,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r3_orders_2(X0,X2,X1) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f113,f65])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_waybel_9(X0,sK2,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(sK2,X0) | r3_orders_2(X0,X2,X1) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(resolution,[],[f66,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_orders_2(X0,X3,X4) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(rectify,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.21/0.46    inference(rectify,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0))) )),
% 0.21/0.46    inference(resolution,[],[f258,f68])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f257,f137])).
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f256,f54])).
% 0.21/0.46  fof(f256,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f255,f55])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f254,f56])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f253,f57])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f252,f58])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f251,f59])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f250,f60])).
% 0.21/0.46  fof(f250,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f249,f61])).
% 0.21/0.46  fof(f249,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f248,f62])).
% 0.21/0.46  fof(f248,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X1) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r3_orders_2(sK0,X1,X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f120,f67])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~l1_waybel_0(sK2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~r3_waybel_9(X3,sK2,X5) | ~v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) | r3_orders_2(X3,X5,X4) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f119,f64])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~r3_waybel_9(X3,sK2,X5) | ~v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(sK2,X3) | r3_orders_2(X3,X5,X4) | v2_struct_0(sK2) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f114,f65])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~r2_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~r3_waybel_9(X3,sK2,X5) | ~v5_pre_topc(k4_waybel_1(X3,sK4(X3)),X3,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(sK2,X3) | r3_orders_2(X3,X5,X4) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.21/0.46    inference(resolution,[],[f66,f102])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X4,X0,X3,X1] : (~v7_waybel_0(X1) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_orders_2(X0,X3,X4) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f50])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    r2_lattice3(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f63,f70,f260])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    l1_orders_2(sK0)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f62,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    v5_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f45])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    k1_waybel_2(sK0,sK2) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.46    inference(forward_demodulation,[],[f142,f132])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    k1_waybel_2(sK0,sK2) = k4_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f111,f67,f126,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_orders_2(X0) | ~l1_waybel_0(X1,X0) | k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_2)).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    k4_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k1_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f126,f111,f138,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v1_relat_1(X1) | k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k4_yellow_2(X0,X1) = k1_yellow_0(X0,k2_relat_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_2)).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    v1_relat_1(u1_waybel_0(sK0,sK2))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f131,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (31275)------------------------------
% 0.21/0.46  % (31275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (31275)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (31275)Memory used [KB]: 6652
% 0.21/0.46  % (31275)Time elapsed: 0.047 s
% 0.21/0.46  % (31275)------------------------------
% 0.21/0.46  % (31275)------------------------------
% 0.21/0.46  % (31259)Success in time 0.109 s
%------------------------------------------------------------------------------
