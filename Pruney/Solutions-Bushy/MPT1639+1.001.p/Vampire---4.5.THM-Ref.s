%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 500 expanded)
%              Number of leaves         :    5 (  86 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (3007 expanded)
%              Number of equality atoms :   20 ( 583 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f124,f19])).

fof(f19,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_0)).

fof(f124,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f123,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f120,f107])).

fof(f107,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f71,f105])).

fof(f105,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f93,f104])).

fof(f104,plain,(
    r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f103,f37])).

fof(f37,plain,(
    r3_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f34,f20])).

fof(f34,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X0) ) ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f31,f22])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X0) ) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f103,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f100,f20])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK1,sK1)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f76,f20])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,sK2) ) ),
    inference(resolution,[],[f68,f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r3_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f67,f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r3_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r3_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f82,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X1,sK1) ) ),
    inference(resolution,[],[f80,f20])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | ~ r3_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | ~ r3_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | ~ r3_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f84,f20])).

fof(f84,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f61,f20])).

fof(f61,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f44,plain,
    ( r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f41,f18])).

fof(f18,plain,(
    k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k5_waybel_0(sK0,X1))
      | ~ r1_orders_2(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f39,f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X1,k5_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X1,k5_waybel_0(sK0,X0)) ) ),
    inference(resolution,[],[f25,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | r2_hidden(X2,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f49,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k5_waybel_0(sK0,X1))
      | r1_orders_2(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f47,f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,k5_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f46,f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,k5_waybel_0(sK0,X0)) ) ),
    inference(resolution,[],[f26,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_orders_2(sK0,X0,sK2) ) ),
    inference(resolution,[],[f80,f17])).

fof(f71,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f70,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f62,f17])).

fof(f62,plain,
    ( ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f49,f18])).

fof(f120,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(resolution,[],[f116,f88])).

fof(f88,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f87,f36])).

fof(f36,plain,(
    r3_orders_2(sK0,sK2,sK2) ),
    inference(resolution,[],[f34,f17])).

fof(f87,plain,
    ( ~ r3_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f83,f17])).

fof(f83,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK2) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f42,f17])).

fof(f42,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f40,f18])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k5_waybel_0(sK0,X0))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f39,f17])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k5_waybel_0(sK0,X0))
      | r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f47,f17])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2 = X0 ) ),
    inference(resolution,[],[f115,f17])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

%------------------------------------------------------------------------------
