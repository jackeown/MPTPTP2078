%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1695+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  256 (1169353 expanded)
%              Number of leaves         :    5 (197680 expanded)
%              Depth                    :  111
%              Number of atoms          : 1208 (8618787 expanded)
%              Number of equality atoms :   41 (58901 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f813,plain,(
    $false ),
    inference(subsumption_resolution,[],[f812,f767])).

fof(f767,plain,(
    ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f766,f646])).

fof(f646,plain,(
    sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f645,f275])).

fof(f275,plain,(
    ~ r1_yellow_0(sK0,sK1) ),
    inference(global_subsumption,[],[f21,f218])).

fof(f218,plain,(
    v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f217,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
             => r1_yellow_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_waybel_0)).

fof(f217,plain,
    ( v24_waybel_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f216,plain,
    ( v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f24])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f215,plain,
    ( v24_waybel_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( v24_waybel_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f196,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK6(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r3_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d39_waybel_0)).

fof(f196,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f195,f71])).

fof(f71,plain,
    ( r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0)) ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK2(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f67,plain,
    ( r1_yellow_0(sK0,sK6(sK0))
    | v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f60])).

fof(f60,plain,
    ( v1_waybel_0(sK6(sK0),sK0)
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f59,f23])).

fof(f59,plain,
    ( v2_struct_0(sK0)
    | v1_waybel_0(sK6(sK0),sK0)
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f57,f24])).

fof(f57,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_waybel_0(sK6(sK0),sK0)
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f26,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | v1_waybel_0(sK6(X0),X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( v24_waybel_0(sK0)
    | ~ v1_waybel_0(sK6(sK0),sK0)
    | v1_xboole_0(sK6(sK0))
    | r1_yellow_0(sK0,sK6(sK0)) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( v24_waybel_0(sK0)
    | ~ v1_waybel_0(sK6(sK0),sK0)
    | v1_xboole_0(sK6(sK0))
    | r1_yellow_0(sK0,sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f62,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_0(X1,sK0)
      | v1_xboole_0(X1)
      | r1_yellow_0(sK0,X1)
      | v24_waybel_0(sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f61,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f26,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f195,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0))) ),
    inference(subsumption_resolution,[],[f194,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0)) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f68,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f194,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0))) ),
    inference(subsumption_resolution,[],[f193,f23])).

fof(f193,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f192,f26])).

fof(f192,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f24])).

fof(f191,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK6(sK0),sK2(sK0,sK6(sK0)))
    | v2_struct_0(sK0)
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f184,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r3_orders_2(X0,X2,sK8(X0,X2))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK6(X0),X2)
      | v2_struct_0(X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f184,plain,
    ( r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0))))
    | v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f92])).

fof(f92,plain,
    ( m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f70])).

fof(f91,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f23])).

fof(f90,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f89,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f24])).

fof(f88,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f71,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_lattice3(X0,sK6(X0),X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f183,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f182,f70])).

fof(f182,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f181,f23])).

fof(f181,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f180,f26])).

fof(f180,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f178,f24])).

fof(f178,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(resolution,[],[f133,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f133,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0))))
    | v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0)) ),
    inference(subsumption_resolution,[],[f132,f67])).

fof(f132,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | r1_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0))))
    | ~ r1_yellow_0(sK0,sK6(sK0)) ),
    inference(subsumption_resolution,[],[f131,f92])).

fof(f131,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0))))
    | ~ r1_yellow_0(sK0,sK6(sK0)) ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f112,plain,
    ( v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0)
    | ~ m1_subset_1(sK8(sK0,sK2(sK0,sK6(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK2(sK0,sK6(sK0)),sK8(sK0,sK2(sK0,sK6(sK0))))
    | ~ r1_yellow_0(sK0,sK6(sK0)) ),
    inference(resolution,[],[f96,f42])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK2(X0,X1),X5)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,
    ( r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0))))
    | v1_xboole_0(sK6(sK0))
    | v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f70])).

fof(f95,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f94,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f93,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(subsumption_resolution,[],[f87,f24])).

fof(f87,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0)))) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( v24_waybel_0(sK0)
    | v1_xboole_0(sK6(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2(sK0,sK6(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK6(sK0),sK8(sK0,sK2(sK0,sK6(sK0))))
    | v24_waybel_0(sK0) ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_lattice3(X0,sK6(X0),X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_lattice3(X0,sK6(X0),sK8(X0,X2))
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f645,plain,
    ( sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f644,f26])).

fof(f644,plain,
    ( ~ l1_orders_2(sK0)
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f643,f254])).

fof(f254,plain,(
    r2_lattice3(sK0,sK1,sK7(sK0,sK1)) ),
    inference(global_subsumption,[],[f18,f218,f253])).

fof(f253,plain,
    ( v1_xboole_0(sK1)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f252,f218])).

fof(f252,plain,
    ( v1_xboole_0(sK1)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f23])).

fof(f251,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f220])).

fof(f220,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(resolution,[],[f218,f19])).

fof(f19,plain,
    ( ~ v24_waybel_0(sK0)
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f250,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f26])).

fof(f249,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f24])).

fof(f242,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f219,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,X1,sK7(X0,X1))
      | ~ v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f219,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f218,f20])).

fof(f20,plain,
    ( ~ v24_waybel_0(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f643,plain,
    ( ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f628,f248])).

fof(f248,plain,(
    m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f18,f218,f247])).

fof(f247,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f246,f218])).

fof(f246,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f245,f23])).

fof(f245,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f220])).

fof(f244,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f26])).

fof(f243,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f24])).

fof(f241,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f219,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f628,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f578,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f578,plain,(
    r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f577,f23])).

fof(f577,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f505])).

fof(f505,plain,(
    m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f504,f293])).

fof(f293,plain,
    ( sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f292,f275])).

fof(f292,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f291,f26])).

fof(f291,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f264,f248])).

fof(f264,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f504,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f503,f492])).

fof(f492,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f491,f287])).

fof(f287,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f286,f275])).

fof(f286,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f285,f26])).

fof(f285,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f262,f248])).

fof(f262,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f491,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f490,f23])).

fof(f490,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f489,f248])).

fof(f489,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f488,f26])).

fof(f488,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f487,f24])).

fof(f487,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f460,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (31404)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f460,plain,
    ( r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f18,f218,f459])).

fof(f459,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f458,f287])).

fof(f458,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f457,f218])).

fof(f457,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f456,f23])).

fof(f456,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f455,f219])).

fof(f455,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f454,f220])).

fof(f454,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f453,f26])).

fof(f453,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f428,f24])).

fof(f428,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f290,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,X3)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,sK7(X0,X1),X3)
      | ~ v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f290,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f289,f275])).

fof(f289,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f288,f26])).

fof(f288,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f263,f248])).

fof(f263,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f503,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f502,f287])).

fof(f502,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f501,f25])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f501,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f500,f248])).

fof(f500,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f494,f26])).

fof(f494,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(resolution,[],[f466,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f466,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f461,f248])).

fof(f461,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1)) ),
    inference(resolution,[],[f269,f254])).

fof(f269,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0) ) ),
    inference(global_subsumption,[],[f21,f218,f268])).

fof(f268,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f267,f26])).

fof(f267,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f255,f248])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f254,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f576,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f575,f248])).

fof(f575,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f574,f26])).

fof(f574,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f573,f24])).

fof(f573,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f568,f56])).

fof(f568,plain,(
    r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(global_subsumption,[],[f18,f218,f567])).

fof(f567,plain,
    ( v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f566,f218])).

fof(f566,plain,
    ( v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f565,f23])).

fof(f565,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f564,f505])).

fof(f564,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f563,f219])).

fof(f563,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f562,f220])).

fof(f562,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f561,f26])).

fof(f561,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f536,f24])).

fof(f536,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f518,f45])).

fof(f518,plain,(
    r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f517,f284])).

fof(f284,plain,
    ( sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f283,f275])).

fof(f283,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f282,f26])).

fof(f282,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f261,f248])).

fof(f261,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) != sK4(sK0,sK1,sK7(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f517,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f516,f486])).

fof(f486,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f485,f278])).

fof(f278,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f277,f275])).

fof(f277,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f276,f26])).

fof(f276,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f259,f248])).

fof(f259,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f485,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f484,f23])).

fof(f484,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f483,f248])).

fof(f483,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f482,f26])).

fof(f482,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f481,f24])).

fof(f481,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f416,f56])).

fof(f416,plain,
    ( r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(global_subsumption,[],[f18,f218,f415])).

fof(f415,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f414,f278])).

fof(f414,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f413,f218])).

fof(f413,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f412,f23])).

fof(f412,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f411,f219])).

fof(f411,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f410,f220])).

fof(f410,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f409,f26])).

fof(f409,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f384,f24])).

fof(f384,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f281,f45])).

fof(f281,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f280,f275])).

fof(f280,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f279,f26])).

fof(f279,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f260,f248])).

fof(f260,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f254,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f516,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f515,f278])).

fof(f515,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f514,f25])).

fof(f514,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f513,f248])).

fof(f513,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f507,f26])).

fof(f507,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(resolution,[],[f479,f54])).

fof(f479,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f474,f248])).

fof(f474,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
    | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1)) ),
    inference(resolution,[],[f272,f254])).

fof(f272,plain,(
    ! [X1] :
      ( ~ r2_lattice3(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X1) ) ),
    inference(global_subsumption,[],[f21,f218,f271])).

fof(f271,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X1)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X1)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f270,f26])).

fof(f270,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X1)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X1)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f256,f248])).

fof(f256,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK7(sK0,sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X1)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X1)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f254,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f766,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f765,f25])).

fof(f765,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f764,f638])).

fof(f638,plain,(
    m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f637,f275])).

fof(f637,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f636,f26])).

fof(f636,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f635,f254])).

fof(f635,plain,
    ( ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f626,f248])).

fof(f626,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f578,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f764,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f763,f248])).

fof(f763,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f762,f26])).

fof(f762,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1))
    | sK7(sK0,sK1) = sK4(sK0,sK1,sK7(sK0,sK1)) ),
    inference(resolution,[],[f745,f54])).

fof(f745,plain,(
    r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f744,f23])).

fof(f744,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f743,f638])).

fof(f743,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f742,f248])).

fof(f742,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f741,f26])).

fof(f741,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f740,f24])).

fof(f740,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f710,f56])).

fof(f710,plain,(
    r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(global_subsumption,[],[f18,f218,f709])).

fof(f709,plain,
    ( v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f708,f218])).

fof(f708,plain,
    ( v1_xboole_0(sK1)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f707,f23])).

fof(f707,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f706,f638])).

fof(f706,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f705,f219])).

fof(f705,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f704,f220])).

fof(f704,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f703,f26])).

% (31412)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f703,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f678,f24])).

fof(f678,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK7(sK0,sK1),sK4(sK0,sK1,sK7(sK0,sK1)))
    | ~ v24_waybel_0(sK0) ),
    inference(resolution,[],[f642,f45])).

fof(f642,plain,(
    r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f641,f275])).

fof(f641,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f640,f26])).

fof(f640,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f639,f254])).

fof(f639,plain,
    ( ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f627,f248])).

fof(f627,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK7(sK0,sK1)))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f578,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f812,plain,(
    r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f799,f248])).

fof(f799,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),sK7(sK0,sK1)) ),
    inference(resolution,[],[f634,f254])).

fof(f634,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f633,f275])).

fof(f633,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f632,f26])).

fof(f632,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f631,f254])).

fof(f631,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f625,f248])).

fof(f625,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,sK7(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1)),X0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f578,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
