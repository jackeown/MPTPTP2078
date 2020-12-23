%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1990+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  122 (4155 expanded)
%              Number of leaves         :   18 ( 831 expanded)
%              Depth                    :   16
%              Number of atoms          :  700 (49542 expanded)
%              Number of equality atoms :   23 ( 243 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f258])).

fof(f258,plain,(
    r2_hidden(sK10(sK0,sK6(sK0,sK1),sK2),sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f67,f64,f65,f69,f63,f57,f58,f163,f175,f59,f174,f173,f253,f184,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X2)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
      | r2_hidden(sK10(X0,X1,X2),X1)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_hidden(X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_finset_1(X2)
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_hidden(X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_finset_1(X2)
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r2_hidden(X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_waybel_7)).

fof(f184,plain,(
    m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f65,f63,f64,f69,f67,f66,f62,f61,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

fof(f61,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X2)
              & ~ v1_xboole_0(X2) )
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X2)
              & ~ v1_xboole_0(X2) )
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_finset_1(X2)
                    & ~ v1_xboole_0(X2) )
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,u1_struct_0(X0))
                         => ~ ( r3_orders_2(X0,X3,X1)
                              & r2_hidden(X3,X2) ) )
                      & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_7)).

fof(f62,plain,(
    v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f253,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f163,f251,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f251,plain,(
    m1_subset_1(k2_yellow_0(sK0,sK2),sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f171,f249,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f249,plain,(
    m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f248,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f248,plain,(
    r1_tarski(k1_waybel_3(sK0,sK1),sK6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f247,f189])).

fof(f189,plain,(
    sK1 = k1_yellow_0(sK0,sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f66,f64,f69,f67,f63,f62,f61,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,sK6(X0,X1)) = X1
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f247,plain,(
    r1_tarski(k1_waybel_3(sK0,k1_yellow_0(sK0,sK6(sK0,sK1))),sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f68,f63,f64,f65,f69,f141,f67,f163,f174,f173,f140,f147,f184,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v24_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X2)
      | ~ v1_waybel_0(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
      | r1_tarski(k1_waybel_3(X0,X1),X2)
      | ~ v3_waybel_3(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( ( ! [X2] :
                  ( r1_tarski(k1_waybel_3(X0,X1),X2)
                  | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( ( ! [X2] :
                  ( r1_tarski(k1_waybel_3(X0,X1),X2)
                  | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v24_waybel_0(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                   => r1_tarski(k1_waybel_3(X0,X1),X2) ) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_5)).

fof(f147,plain,(
    ! [X0] : r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f136,f69,f63,f61,f140,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f136,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f69,f67,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f140,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f141,plain,(
    v24_waybel_0(sK0) ),
    inference(unit_resulting_resolution,[],[f69,f68,f63,f136,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_waybel_3)).

fof(f68,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f171,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),k1_waybel_3(sK0,sK1)) ),
    inference(forward_demodulation,[],[f170,f144])).

fof(f144,plain,(
    k1_waybel_3(sK0,sK1) = a_2_0_waybel_3(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f63,f136,f69,f61,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_3)).

fof(f170,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f136,f63,f69,f60,f139,f61,f135])).

fof(f135,plain,(
    ! [X2,X3,X1] :
      ( ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X3,a_2_0_waybel_3(X1,X2)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_3)).

fof(f139,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f60,plain,(
    r1_waybel_3(sK0,k2_yellow_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f173,plain,(
    v1_waybel_0(sK6(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f64,f69,f67,f63,f62,f61,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_waybel_0(sK6(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f174,plain,(
    v12_waybel_0(sK6(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f64,f69,f67,f63,f62,f61,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v12_waybel_0(sK6(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f175,plain,(
    v1_waybel_7(sK6(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f64,f69,f67,f63,f62,f61,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_waybel_7(sK6(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    ~ v1_xboole_0(sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f63,f64,f69,f67,f66,f62,f61,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK6(X0,X1))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v1_finset_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f290,plain,(
    ~ r2_hidden(sK10(sK0,sK6(sK0,sK1),sK2),sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f190,f61,f263,f288,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f288,plain,(
    ~ r1_orders_2(sK0,sK10(sK0,sK6(sK0,sK1),sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f63,f69,f136,f61,f263,f275,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f275,plain,(
    ~ r3_orders_2(sK0,sK10(sK0,sK6(sK0,sK1),sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f254,f263,f56])).

fof(f56,plain,(
    ! [X3] :
      ( ~ r3_orders_2(sK0,X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f254,plain,(
    r2_hidden(sK10(sK0,sK6(sK0,sK1),sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f67,f64,f58,f69,f63,f57,f65,f163,f175,f59,f174,f173,f184,f253,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X2)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
      | r2_hidden(sK10(X0,X1,X2),X2)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f263,plain,(
    m1_subset_1(sK10(sK0,sK6(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f67,f63,f65,f69,f58,f57,f64,f163,f175,f59,f174,f173,f253,f184,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
      | ~ v3_orders_2(X0)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f190,plain,(
    r2_lattice3(sK0,sK6(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f187,f189])).

fof(f187,plain,(
    r2_lattice3(sK0,sK6(sK0,sK1),k1_yellow_0(sK0,sK6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f69,f65,f140,f185,f132])).

fof(f132,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,axiom,(
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

fof(f185,plain,(
    r1_yellow_0(sK0,sK6(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f141,f136,f65,f63,f69,f163,f173,f184,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_yellow_0(X0,X1)
      | ~ v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_waybel_0)).

%------------------------------------------------------------------------------
