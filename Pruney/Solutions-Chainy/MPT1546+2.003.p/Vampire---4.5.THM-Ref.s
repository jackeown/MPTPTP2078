%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 947 expanded)
%              Number of leaves         :    7 ( 162 expanded)
%              Depth                    :   39
%              Number of atoms          :  485 (5678 expanded)
%              Number of equality atoms :   77 ( 711 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f310])).

fof(f310,plain,(
    ~ r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f130,f309])).

fof(f309,plain,(
    sK1 = k10_lattice3(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | sK1 = k10_lattice3(sK0,sK1,sK2) ),
    inference(superposition,[],[f260,f111])).

fof(f111,plain,(
    k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f75,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f73,f30])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f71,f29])).

fof(f29,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2) ) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

fof(f260,plain,
    ( sK1 = k10_lattice3(sK0,sK2,sK1)
    | sK1 = k10_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f259,f129])).

fof(f129,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k10_lattice3(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f23,f123])).

fof(f123,plain,(
    k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f86,f25])).

fof(f86,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f85,f28])).

fof(f85,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f80,f29])).

fof(f80,plain,(
    ! [X1] :
      ( ~ v1_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1) ) ),
    inference(resolution,[],[f43,f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (32045)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f23,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f259,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f258,f28])).

fof(f258,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f257,f150])).

fof(f150,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f149,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f54,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f149,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f26])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f30])).

fof(f147,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f27])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f146,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f107,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f107,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f64,f25])).

fof(f64,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f63,f55])).

fof(f63,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f58,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,sK1) ) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f257,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f256,f26])).

fof(f256,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f255,f25])).

fof(f255,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f254,f30])).

fof(f254,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f253,f29])).

fof(f253,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(resolution,[],[f229,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(f229,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | sK1 = k10_lattice3(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | sK1 = k10_lattice3(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1)) ),
    inference(forward_demodulation,[],[f227,f111])).

fof(f227,plain,
    ( sK1 = k10_lattice3(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f216,f26])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k10_lattice3(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(resolution,[],[f150,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k10_lattice3(sK0,sK1,sK2)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0) ) ),
    inference(backward_demodulation,[],[f94,f123])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f92,f26])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1))
      | sK1 = k10_lattice3(sK0,sK2,X0)
      | sK1 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(resolution,[],[f51,f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X3)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f34,f31])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f130,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 != k10_lattice3(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f24,f123])).

fof(f24,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f324,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f323,f28])).

fof(f323,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f322,f25])).

fof(f322,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f321,f30])).

fof(f321,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f320,f29])).

fof(f320,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f318,f26])).

fof(f318,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(superposition,[],[f48,f311])).

fof(f311,plain,(
    sK1 = k10_lattice3(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f111,f309])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f45,f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:17:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (32040)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (32038)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (32032)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (32032)Refutation not found, incomplete strategy% (32032)------------------------------
% 0.21/0.48  % (32032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32048)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (32037)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (32032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32032)Memory used [KB]: 10618
% 0.21/0.50  % (32032)Time elapsed: 0.061 s
% 0.21/0.50  % (32032)------------------------------
% 0.21/0.50  % (32032)------------------------------
% 0.21/0.50  % (32034)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (32051)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (32033)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (32051)Refutation not found, incomplete strategy% (32051)------------------------------
% 0.21/0.50  % (32051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32051)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32051)Memory used [KB]: 10618
% 0.21/0.50  % (32051)Time elapsed: 0.080 s
% 0.21/0.50  % (32051)------------------------------
% 0.21/0.50  % (32051)------------------------------
% 0.21/0.50  % (32048)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f324,f310])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f130,f309])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f300])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | sK1 = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(superposition,[],[f260,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    k10_lattice3(sK0,sK2,sK1) = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f75,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((k13_lattice3(X0,X1,X2) = X1 <~> r1_orders_2(X0,X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((k13_lattice3(X0,X1,X2) = X1 <~> r1_orders_2(X0,X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X1 <=> r1_orders_2(X0,X2,X1)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X1 <=> r1_orders_2(X0,X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X0) = k10_lattice3(sK0,X0,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f39,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK2,sK1) | sK1 = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK2,sK1) | sK1 = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f23,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f86,f25])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f28])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f30])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f29])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,X1) = k13_lattice3(sK0,sK1,X1)) )),
% 0.21/0.50    inference(resolution,[],[f43,f26])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  % (32045)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK2,sK1) | sK1 = k13_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f28])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f257,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f54,f30])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f31,f29])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f26])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f30])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f146,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f107,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    r3_orders_2(sK0,sK1,sK1)),
% 0.21/0.50    inference(resolution,[],[f64,f25])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f55])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f62,f30])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f27])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X1] : (~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)) )),
% 0.21/0.50    inference(resolution,[],[f40,f26])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f256,f26])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f255,f25])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f254,f30])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f29])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f248])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK1,sK1) | ~v5_orders_2(sK0) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f229,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f35,f31])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1)) | sK1 = k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | sK1 = k10_lattice3(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f227,f111])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1)) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f216,f26])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k10_lattice3(sK0,sK1,sK2) | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1)) | sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f150,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k10_lattice3(sK0,sK1,sK2) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f94,f123])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f28])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f92,f26])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f25])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f30])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f29])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK3(sK0,sK2,X0,sK1)) | sK1 = k10_lattice3(sK0,sK2,X0) | sK1 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f51,f23])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f34,f31])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK2,sK1) | sK1 != k10_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f24,f123])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK2,sK1) | sK1 != k13_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f323,f28])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f322,f25])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f321,f30])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f29])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f318,f26])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f315])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.50    inference(superposition,[],[f48,f311])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    sK1 = k10_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f111,f309])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f45,f31])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (32048)------------------------------
% 0.21/0.50  % (32048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32048)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (32048)Memory used [KB]: 1791
% 0.21/0.50  % (32048)Time elapsed: 0.079 s
% 0.21/0.50  % (32048)------------------------------
% 0.21/0.50  % (32048)------------------------------
% 0.21/0.50  % (32030)Success in time 0.138 s
%------------------------------------------------------------------------------
