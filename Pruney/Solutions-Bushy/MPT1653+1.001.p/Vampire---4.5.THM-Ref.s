%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 217 expanded)
%              Number of leaves         :    6 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 (1116 expanded)
%              Number of equality atoms :   12 ( 132 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f247,f262])).

fof(f262,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f260,f233])).

fof(f233,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_2
  <=> r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f260,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f259,f86])).

fof(f86,plain,(
    m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f85,f12])).

fof(f12,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
             => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_0)).

fof(f85,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f84,f17])).

% (27253)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f17,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f75,f14])).

fof(f14,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | sQ3_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(equality_proxy_replacement,[],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f24,plain,(
    ~ sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f13,f23])).

fof(f13,plain,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f258,f11])).

fof(f11,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f258,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f257,f17])).

fof(f257,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f256,f16])).

fof(f16,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f256,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f255,f15])).

fof(f15,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f255,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f254,f14])).

fof(f254,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(resolution,[],[f230,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_0)).

fof(f230,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl4_1
  <=> r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f247,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f245,f24])).

fof(f245,plain,
    ( sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f244,f241])).

fof(f241,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f236,f86])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f234,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | r2_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f66,f16])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | r2_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f65,f15])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | r2_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f63,f14])).

fof(f63,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | r2_lattice3(sK0,sK1,X0) ) ),
    inference(resolution,[],[f11,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f234,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f244,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f243,f12])).

fof(f243,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f242,f17])).

fof(f242,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f238,f14])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | sQ3_eqProxy(k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f234,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | sQ3_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(equality_proxy_replacement,[],[f21,f23])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f235,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f80,f232,f228])).

fof(f80,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f79,f12])).

fof(f79,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f78,f17])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f73,f14])).

fof(f73,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | sQ3_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(equality_proxy_replacement,[],[f20,f23])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
