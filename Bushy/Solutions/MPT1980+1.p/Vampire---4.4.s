%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t29_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 7.66s
% Output     : Refutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  110 (4173 expanded)
%              Number of leaves         :   15 ( 856 expanded)
%              Depth                    :    8
%              Number of atoms          :  600 (63133 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1512,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f491,f680,f1480,f496,f1483,f1485,f1486,f81])).

fof(f81,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK2,X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_7(X3,sK0)
      | v1_xboole_0(X3)
      | ~ r1_subset_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v13_waybel_0(X3,X0)
                          & v2_waybel_0(X3,X0)
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_subset_1(X1,X3)
                            & r1_tarski(X2,X3)
                            & v2_waybel_7(X3,X0) ) )
                    & r1_subset_1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t29_waybel_7)).

fof(f1486,plain,(
    m1_subset_1(sK3(k7_lattice3(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f97,f492,f494,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0)))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t27_yellow_7)).

fof(f494,plain,(
    m1_subset_1(sK3(k7_lattice3(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t27_waybel_7)).

fof(f279,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    inference(unit_resulting_resolution,[],[f97,f88,f90,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t26_yellow_7)).

fof(f90,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f234,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    inference(unit_resulting_resolution,[],[f97,f83,f85,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0)))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    v2_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f235,plain,(
    v1_waybel_0(sK2,k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f83,f85,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_waybel_0(X1,k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f233,plain,(
    v12_waybel_0(sK2,k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f84,f85,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v12_waybel_0(X1,k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t29_yellow_7)).

fof(f84,plain,(
    v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f278,plain,(
    v2_waybel_0(sK1,k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f88,f90,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_waybel_0(X1,k7_lattice3(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f276,plain,(
    v13_waybel_0(sK1,k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f89,f90,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t28_yellow_7)).

fof(f89,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f209,plain,(
    v3_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f97,f149])).

fof(f149,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc1_yellow_7)).

fof(f91,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f203,plain,(
    v2_waybel_1(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f92,f94,f96,f95,f93,f97,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v2_waybel_1(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v2_waybel_1(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v2_waybel_1(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc8_yellow_7)).

fof(f93,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    v2_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f199,plain,(
    v1_lattice3(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f96,f97,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc5_yellow_7)).

fof(f205,plain,(
    v5_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f93,f97,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc3_yellow_7)).

fof(f201,plain,(
    v2_lattice3(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f95,f97,f141])).

fof(f141,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc6_yellow_7)).

fof(f211,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f97,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_orders_2(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',dt_k7_lattice3)).

fof(f229,plain,(
    r1_subset_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f82,f87,f86,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ r1_subset_1(X0,X1)
      | r1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',symmetry_r1_subset_1)).

fof(f86,plain,(
    r1_subset_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f207,plain,(
    v4_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f92,f97,f147])).

fof(f147,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',fc2_yellow_7)).

fof(f87,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f492,plain,(
    v1_waybel_0(sK3(k7_lattice3(sK0),sK2,sK1),k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v1_waybel_0(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1485,plain,(
    v2_waybel_0(sK3(k7_lattice3(sK0),sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f97,f492,f494,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0)))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1483,plain,(
    v13_waybel_0(sK3(k7_lattice3(sK0),sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f97,f493,f494,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0)))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f493,plain,(
    v12_waybel_0(sK3(k7_lattice3(sK0),sK2,sK1),k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v12_waybel_0(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f496,plain,(
    r1_tarski(sK2,sK3(k7_lattice3(sK0),sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | r1_tarski(X1,sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1480,plain,(
    v2_waybel_7(sK3(k7_lattice3(sK0),sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f96,f97,f95,f93,f92,f91,f491,f495,f493,f492,f494,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,k7_lattice3(X0))
      | ~ v12_waybel_0(X1,k7_lattice3(X0))
      | ~ v1_waybel_7(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t29_waybel_7.p',t21_waybel_7)).

fof(f495,plain,(
    v1_waybel_7(sK3(k7_lattice3(sK0),sK2,sK1),k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | v1_waybel_7(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f680,plain,(
    r1_subset_1(sK1,sK3(k7_lattice3(sK0),sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f87,f491,f497,f115])).

fof(f497,plain,(
    r1_subset_1(sK3(k7_lattice3(sK0),sK2,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f82,f87,f207,f229,f211,f201,f205,f199,f203,f209,f276,f278,f233,f235,f234,f279,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | r1_subset_1(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f491,plain,(
    ~ v1_xboole_0(sK3(k7_lattice3(sK0),sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f82,f87,f205,f229,f211,f201,f207,f199,f203,f209,f276,f278,f233,f235,f234,f279,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ v1_xboole_0(sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
